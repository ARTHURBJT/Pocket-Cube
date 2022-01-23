(*Resolution du pocket cube (ou rubik's cube 2x2)*)

type couleur = Blanc | Bleu | Orange | Vert | Rouge | Jaune;;

type coin = couleur * couleur * couleur;;

type cube = coin array;;

type ope_elementaires = D | H | F | D' | H' | F';;

type formule = ope_elementaires list;;


let cree_copie cube =
  let cube0 = Array.make 8 (Blanc, Bleu, Rouge) in
        for i = 0 to 7 do
            cube0.(i) <- cube.(i) done;
        cube0;;


(*Sens horaire*)
let tourne_coin1 (coin: coin) = match coin with
   | (c1, c2, c3) -> ((c3, c1, c2): coin);;


(*Sens anti-horaire*)
let tourne_coin2 (coin: coin) = match coin with
   | (c1, c2, c3) -> ((c2, c3, c1): coin);;


let deplace_coins_cycle cube l =
   if (List.length l) < 4 then failwith "la liste ne convient pas"
   else match l with
      | a :: q ->
      let coin0 = cube.(a) in

      let rec aux l0 = match l0 with
         | [] -> ()
         | [d0] -> cube.(d0) <- coin0
         | a0 :: b0 :: q0 ->
            begin
               cube.(a0) <- cube.(b0);
               aux (b0 :: q0)
            end in

      aux l;;


let rec corrige_coins cube l1 l2 = match (l1, l2) with
   | ([], _) -> ()
   | (_, []) -> ()
   | (p1 :: q1, 0 :: q2) -> corrige_coins cube q1 q2
   | (p1 :: q1, 1 :: q2) ->
      cube.(p1) <- tourne_coin1 cube.(p1);
      corrige_coins cube q1 q2
   | (p1 :: q1, _ :: q2) ->
      cube.(p1) <- tourne_coin2 cube.(p1);
      corrige_coins cube q1 q2;;


(*modification_cube est une fonction purement auxiliare très utilisee ensuite*)
let modification_cube cube l1 l2=
   deplace_coins_cycle cube l1;
   corrige_coins cube l1 l2;;


(*D1, H1, F1 indiques une rotation d'un quart de tour dans le sens classique : sens horaire.
D2, H2, F2 indiques une rotation d'un quart de tour dans le sens anti-horaire.*)
let tourneD1 cube =
   let cube1 = cree_copie cube in
         let l1 = [1; 5; 6; 2] in
               let l2 = [0; 1; 1; 1] in
                  modification_cube cube1 l1 l2;
                  cube1;;


let tourneD2 cube =
   let cube1 = cree_copie cube in
         let l1 = [1; 2; 6; 5] in
               let l2 = [2; 2; 2; 0] in
                  modification_cube cube1 l1 l2;
                  cube1;;


let tourneH1 cube =
   let cube1 = cree_copie cube in
         let l1 = [0; 1; 2; 3] in
               let l2 = [0; 0; 0; 0] in
                  modification_cube cube1 l1 l2;
                  cube1;;


let tourneH2 cube =
   let cube1 = cree_copie cube in
         let l1 = [0; 3; 2; 1] in
               let l2 = [0; 0; 0; 0] in
                  modification_cube cube1 l1 l2;
                  cube1;;


let tourneF1 cube =
   let cube1 = cree_copie cube in
         let l1 = [0; 4; 5; 1] in
               let l2 = [0; 1; 1; 1] in
                  modification_cube cube1 l1 l2;
                  cube1;;


let tourneF2 cube =
   let cube1 = cree_copie cube in
         let l1 = [0; 1; 5; 4] in
               let l2 = [2; 2; 2; 0] in
                  modification_cube cube1 l1 l2;
                  cube1;;


let tourne ope cube = match ope with
  | D -> tourneD1 cube
  | H -> tourneH1 cube
  | F -> tourneF1 cube
  | D' -> tourneD2 cube
  | H' -> tourneH2 cube
  | F' -> tourneF2 cube;;


let rec applique_formule (f: formule) (cube:cube) = match f with
   | [] -> cube
   | ope :: q -> applique_formule q (tourne ope cube);;
    
    
let rec suppr_coups_inutiles (l: formule) = match l with
  | [] -> l
  | [a] -> l

  | D :: D :: D :: q -> suppr_coups_inutiles (D' :: q)
  | H :: H :: H :: q -> suppr_coups_inutiles (H' :: q)
  | F :: F :: F :: q -> suppr_coups_inutiles (F' :: q)

  | D' :: D' :: D' :: q -> suppr_coups_inutiles (D :: q)
  | H' :: H' :: H' :: q -> suppr_coups_inutiles (H :: q)
  | F' :: F' :: F' :: q -> suppr_coups_inutiles (F :: q)

  | D :: D' :: q -> suppr_coups_inutiles q
  | H :: H' :: q -> suppr_coups_inutiles q
  | F :: F' :: q -> suppr_coups_inutiles q

  | D' :: D' :: q -> suppr_coups_inutiles (D :: D :: q)
  | H' :: H' :: q -> suppr_coups_inutiles (H :: H :: q)
  | F' :: F' :: q -> suppr_coups_inutiles (F :: F :: q)

  | D' :: D :: q -> suppr_coups_inutiles q
  | H' :: H :: q -> suppr_coups_inutiles q
  | F' :: F :: q -> suppr_coups_inutiles q

  |p :: q -> p :: (suppr_coups_inutiles q);;


(*a ^^ b = a exposant b*)
let rec (^^) a b = 
  if b=0 then 1
  else a*(a^^(b-1));;


(*l est une liste de liste, on ajoute e a chacune de ces sous listes.*)
let ajt_lettre_liste e l = 
  
  let rec aux e0 l0 l1 = match l0 with
  | [] -> l1
  | p :: q -> aux e0 q ((e0::p) :: l1)
  in
  
  aux e l [];;


(*Cette fonction cree la liste de toutes les formules possibles de longueur k, et même un peu trop... Il y a des doublons*)
let rec creer_liste_formules k =
  if k=0 then [[]]
  else 
    let t1=creer_liste_formules (k-1) in
      (ajt_lettre_liste D t1) @ (ajt_lettre_liste D' t1) @ (ajt_lettre_liste H t1) @ (ajt_lettre_liste H' t1) @ (ajt_lettre_liste F t1) @ (ajt_lettre_liste F' t1) @ t1
      ;;


let code_ope ope = match ope with
  | D -> 1
  | D' -> 2
  | H -> 3
  | H' -> 4
  | F -> 5
  | F' -> 6;;


let codifie_formule f = 

  let rec aux f0 c i = match f0 with
  | []-> c
  | p::q -> aux q (c+(code_ope p)*(7^^i)) (i+1)
  in

  aux f 0 0;;

  
let nettoie l=
  let t = Array.make 818727 false in

  let rec aux l0 l1 = match l0 with
    | [] -> l1
    | p::q -> 
      let p1 = suppr_coups_inutiles p in
      let c = codifie_formule p1 in
      if t.(c) then aux q l1
      else (t.(c) <- true ; aux q (p1::l1))
      in

      aux l [];;


let code_couleur couleur = match couleur with
  | Blanc -> 0
  | Bleu -> 1
  | Rouge -> 2
  | Jaune -> 3
  | Vert -> 4
  | Orange -> 5;;


let code_coins (coin:coin) = match coin with
   | (Orange,Jaune,Bleu) -> 0
   | (Blanc,Bleu,Rouge) -> 1
   | (Bleu,Rouge,Blanc) -> 2
   | (Rouge,Blanc,Bleu) -> 3
   | (Blanc,Orange,Bleu) -> 4
   | (Orange,Bleu,Blanc) -> 5
   | (Bleu,Blanc,Orange) -> 6
   | (Blanc,Vert,Orange) -> 7
   | (Vert,Orange,Blanc) -> 8
   | (Orange,Blanc,Vert) -> 9
   | (Blanc,Rouge,Vert) -> 10
   | (Rouge,Vert,Blanc) -> 11
   | (Vert,Blanc,Rouge) -> 12
   | (Jaune,Rouge,Bleu) -> 13
   | (Rouge,Bleu,Jaune) -> 14
   | (Bleu,Jaune,Rouge) -> 15
   | (Jaune,Vert,Rouge) -> 16
   | (Vert,Rouge,Jaune) -> 17
   | (Rouge,Jaune,Vert) -> 18
   | (Jaune,Orange,Vert) -> 19
   | (Orange,Vert,Jaune) -> 20
   | (Vert,Jaune,Orange) -> 21
   | (Jaune,Bleu,Orange) -> 22
   | (Bleu,Orange,Jaune) -> 23
   | _ -> failwith "le cube rentré n'est pas correcte";;


let codifie_cube (cube:cube) = 
  let n = ref 0 in
  let k = ref 0 in
  for i = 0 to 7 do
    let a = code_coins cube.(i) in
         (n:= !n + a * (24 ^^ !k) ; k:= !k + 1)
  done;

  !n;;


(*Cette fonction transforme une liste de formules en une liste de codes de cubes*)
let creer_liste_codes_cubes lf cube0=

  let rec aux lf0 l= match lf0 with
    | [] -> List.rev l
    | pf::qf -> aux qf ((codifie_cube (applique_formule pf cube0)) :: l)
    in

    aux lf [];;


(*Cette fonction inverse une formule. Si on applique f à un cube, alors il faudra appliquer "inverse f"
pour revenir a la position de depart*)
let inverse f = 

  let rec aux f1 f2 = match f1 with
  | [] -> f2
  | D :: q -> aux q (D' ::f2)
  | H :: q -> aux q (H' :: f2)
  | F :: q -> aux q (F' :: f2)
  | D' :: q -> aux q (D :: f2)
  | H' :: q -> aux q (H :: f2)
  | F' :: q -> aux q (F :: f2) in
  
  aux f [];; 


let separe_it lc lf=
  let n = ref ((List.length lc) / 2) in
  let lc1 = ref [] in
  let lf1 = ref [] in
  let lc2 = ref lc in
  let lf2 = ref lf in
      while !n<>0 do
        match (!lc2,!lf2) with
        | ([],_)->(n:=0)
        | (_,[])->(n:=0)
        | (pc::qc,pf::qf) -> (lc1:=pc::!lc1 ; lc2:=qc ; lf1:=pf::!lf1 ; lf2:=qf ; n:=!n-1)
      done;
        ((List.rev !lc1,List.rev !lf1),(!lc2,!lf2));;

  
let fusion_it couple1 couple2 = 
  match (couple1,couple2) with
  | ((lc1,lf1),(lc2,lf2)) ->
    let n = (List.length lc1 + List.length lc2) in
    let k = ref 0 in
    let lc01 = ref lc1 in
    let lc02 = ref lc2 in
    let lf01 = ref lf1 in
    let lf02 = ref lf2 in
    let lc = ref [] in
    let lf = ref [] in
    while !k <> n do
      match (!lc01,!lf01,!lc02,!lf02) with
        | ([],_,[],_) -> (k := n)
        | (_,[],_,[]) -> (k := n)
        | (_,[],[],_) -> (k := n)
        | ([],_,_,[]) -> (k := n)
        | ([],_,pc2::qc2,pf2::qf2) -> (lc:= pc2 :: !lc ; lc02 := qc2 ; lf:= pf2 :: !lf ; lf02 := qf2 ; k := !k + 1)
        | (_,[],pc2::qc2,pf2::qf2) -> (lc:= pc2 :: !lc ; lc02 := qc2 ; lf:= pf2 :: !lf ; lf02 := qf2 ; k := !k + 1)
        | (pc1::qc1,pf1::qf1,[],_) -> (lc:= pc1 :: !lc ; lc01 := qc1 ; lf:= pf1 :: !lf ; lf01 := qf1 ; k := !k + 1)
        | (pc1::qc1,pf1::qf1,_,[]) -> (lc:= pc1 :: !lc ; lc01 := qc1 ; lf:= pf1 :: !lf ; lf01 := qf1 ; k := !k + 1)
        | (pc1::qc1,pf1::qf1,pc2::qc2,pf2::qf2) -> 
          if pc1 > pc2 then (lc:= pc2 :: !lc ; lc02 := qc2 ; lf:= pf2 :: !lf ; lf02 := qf2 ; k := !k + 1)
          else (lc:= pc1 :: !lc ; lc01 := qc1 ; lf:= pf1 :: !lf ; lf01 := qf1 ; k := !k + 1)
    done;
    (List.rev !lc,List.rev !lf);;

  
let rec tri_fusion lc lf = match lc with
  | [] -> ([],[])
  | [a] -> ([a],lf)
  | _ -> match separe_it lc lf with
    | ((lc1,lf1), (lc2,lf2)) -> fusion_it (tri_fusion lc1 lf1) (tri_fusion lc2 lf2);;


let rec point_intersection lc1 l1 lc2 l2 c n= match (lc1,l1,lc2,l2) with
  | ([],_,_,_) -> c
  | (_,[],_,_) -> c
  | (_,_,[],_) -> c
  | (_,_,_,[]) -> c
  | (pc1::qc1, p1::q1, pc2::qc2, p2::q2) -> 
    if pc1>pc2 then point_intersection lc1 l1 qc2 q2 c n
    else 
      if pc1<pc2 then point_intersection qc1 q1 lc2 l2 c n
      else 
        let sol = suppr_coups_inutiles (p1 @ (inverse p2)) in
          let m = List.length sol in
            if m < n then point_intersection qc1 q1 qc2 q2 sol m
            else point_intersection qc1 q1 qc2 q2 c n ;;


let trouve_cube_fait cube = match cube.(7) with
  |(Vert, Rouge, Jaune) -> [|(Blanc, Bleu, Rouge); (Blanc, Orange, Bleu); (Blanc, Vert, Orange); (Blanc, Rouge, Vert); (Rouge, Bleu, Jaune); (Bleu, Orange, Jaune); (Orange, Vert, Jaune); (Vert, Rouge, Jaune)|]
  |(Rouge, Bleu, Jaune) -> [|(Blanc, Orange, Bleu); (Blanc, Vert, Orange); (Blanc, Rouge, Vert); (Blanc, Bleu, Rouge); (Bleu, Orange, Jaune); (Orange, Vert, Jaune); (Vert, Rouge, Jaune); (Rouge, Bleu, Jaune)|]
  |(Bleu, Orange, Jaune) -> [|(Blanc, Vert, Orange); (Blanc, Rouge, Vert); (Blanc, Bleu, Rouge); (Blanc, Orange, Bleu); (Orange, Vert, Jaune); (Vert, Rouge, Jaune); (Rouge, Bleu, Jaune); (Bleu, Orange, Jaune)|]
  |(Orange, Vert, Jaune) -> [|(Blanc, Rouge, Vert); (Blanc, Bleu, Rouge); (Blanc, Orange, Bleu); (Blanc, Vert, Orange); (Vert, Rouge, Jaune); (Rouge, Bleu, Jaune); (Bleu, Orange, Jaune); (Orange, Vert, Jaune)|]

  |(Vert, Blanc, Rouge) -> [|(Orange, Bleu, Blanc); (Orange, Jaune, Bleu); (Orange, Vert, Jaune); (Orange, Blanc, Vert); (Blanc, Bleu, Rouge); (Bleu, Jaune, Rouge); (Jaune, Vert, Rouge); (Vert, Blanc, Rouge)|]
  |(Blanc, Bleu, Rouge) -> [|(Orange, Jaune, Bleu); (Orange, Vert, Jaune); (Orange, Blanc, Vert); (Orange, Bleu, Blanc); (Bleu, Jaune, Rouge); (Jaune, Vert, Rouge); (Vert, Blanc, Rouge); (Blanc, Bleu, Rouge)|]
  |(Bleu, Jaune, Rouge) -> [|(Orange, Vert, Jaune); (Orange, Blanc, Vert); (Orange, Bleu, Blanc); (Orange, Jaune, Bleu); (Jaune, Vert, Rouge); (Vert, Blanc, Rouge); (Blanc, Bleu, Rouge); (Bleu, Jaune, Rouge)|]
  |(Jaune, Vert, Rouge) -> [|(Orange, Blanc, Vert); (Orange, Bleu, Blanc); (Orange, Jaune, Bleu); (Orange, Vert, Jaune); (Vert, Blanc, Rouge); (Blanc, Bleu, Rouge); (Bleu, Jaune, Rouge); (Jaune, Vert, Rouge)|]

  |(Jaune, Orange, Vert) -> [|(Bleu, Blanc, Orange); (Bleu, Rouge, Blanc); (Bleu, Jaune, Rouge); (Bleu, Orange, Jaune); (Orange, Blanc, Vert); (Blanc, Rouge, Vert); (Rouge, Jaune, Vert); (Jaune, Orange, Vert)|]
  |(Orange, Blanc, Vert) -> [|(Bleu, Blanc, Orange); (Bleu, Rouge, Blanc); (Bleu, Jaune, Rouge); (Bleu, Orange, Jaune); (Blanc, Rouge, Vert); (Rouge, Jaune, Vert); (Jaune, Orange, Vert); (Orange, Blanc, Vert)|]
  |(Blanc, Rouge, Vert) -> [|(Bleu, Blanc, Orange); (Bleu, Rouge, Blanc); (Bleu, Jaune, Rouge); (Bleu, Orange, Jaune); (Rouge, Jaune, Vert); (Jaune, Orange, Vert); (Orange, Blanc, Vert); (Blanc, Rouge, Vert)|]
  |(Rouge, Jaune, Vert) -> [|(Bleu, Blanc, Orange); (Bleu, Rouge, Blanc); (Bleu, Jaune, Rouge); (Bleu, Orange, Jaune); (Jaune, Orange, Vert); (Orange, Blanc, Vert); (Blanc, Rouge, Vert); (Rouge, Jaune, Vert)|]

  |(Rouge, Vert, Blanc) -> [|(Jaune, Orange, Vert); (Jaune, Bleu, Orange); (Jaune, Rouge, Bleu); (Jaune, Vert, Rouge); (Vert, Orange, Blanc); (Orange, Bleu, Blanc); (Bleu, Rouge, Blanc); (Rouge, Vert, Blanc)|]
  |(Vert, Orange, Blanc) -> [|(Jaune, Bleu, Orange); (Jaune, Rouge, Bleu); (Jaune, Vert, Rouge); (Jaune, Orange, Vert); (Orange, Bleu, Blanc); (Bleu, Rouge, Blanc); (Rouge, Vert, Blanc); (Vert, Orange, Blanc)|]
  |(Orange, Bleu, Blanc) -> [|(Jaune, Rouge, Bleu); (Jaune, Vert, Rouge); (Jaune, Orange, Vert); (Jaune, Bleu, Orange); (Bleu, Rouge, Blanc); (Rouge, Vert, Blanc); (Vert, Orange, Blanc); (Orange, Bleu, Blanc)|]
  |(Bleu, Rouge, Blanc) -> [|(Jaune, Vert, Rouge); (Jaune, Orange, Vert); (Jaune, Bleu, Orange); (Jaune, Rouge, Bleu); (Rouge, Vert, Blanc); (Vert, Orange, Blanc); (Orange, Bleu, Blanc); (Bleu, Rouge, Blanc)|]

  |(Jaune, Rouge, Bleu) -> [|(Vert, Blanc, Rouge); (Vert, Orange, Blanc); (Vert, Jaune, Orange); (Vert, Rouge, Jaune); (Rouge, Blanc, Bleu); (Blanc, Orange, Bleu); (Orange, Jaune, Bleu); (Jaune, Rouge, Bleu)|]
  |(Rouge, Blanc, Bleu) -> [|(Vert, Orange, Blanc); (Vert, Jaune, Orange); (Vert, Rouge, Jaune); (Vert, Blanc, Rouge); (Blanc, Orange, Bleu); (Orange, Jaune, Bleu); (Jaune, Rouge, Bleu); (Rouge, Blanc, Bleu)|]
  |(Blanc, Orange, Bleu) -> [|(Vert, Jaune, Orange); (Vert, Rouge, Jaune); (Vert, Blanc, Rouge); (Vert, Orange, Blanc); (Orange, Jaune, Bleu); (Jaune, Rouge, Bleu); (Rouge, Blanc, Bleu); (Blanc, Orange, Bleu)|]
  |(Orange, Jaune, Bleu) -> [|(Vert, Rouge, Jaune); (Vert, Blanc, Rouge); (Vert, Orange, Blanc); (Vert, Jaune, Orange); (Jaune, Rouge, Bleu); (Rouge, Blanc, Bleu); (Blanc, Orange, Bleu); (Orange, Jaune, Bleu)|]

  |(Vert, Jaune, Orange) -> [|(Rouge, Bleu, Jaune); (Rouge, Blanc, Bleu); (Rouge, Vert, Blanc); (Rouge, Jaune, Vert); (Jaune, Bleu, Orange); (Bleu, Blanc, Orange); (Blanc, Vert, Orange); (Vert, Jaune, Orange)|]
  |(Jaune, Bleu, Orange) -> [|(Rouge, Blanc, Bleu); (Rouge, Vert, Blanc); (Rouge, Jaune, Vert); (Rouge, Bleu, Jaune); (Bleu, Blanc, Orange); (Blanc, Vert, Orange); (Vert, Jaune, Orange); (Jaune, Bleu, Orange)|]
  |(Bleu, Blanc, Orange) -> [|(Rouge, Vert, Blanc); (Rouge, Jaune, Vert); (Rouge, Bleu, Jaune); (Rouge, Blanc, Bleu); (Blanc, Vert, Orange); (Vert, Jaune, Orange); (Jaune, Bleu, Orange); (Bleu, Blanc, Orange)|]
  |(Blanc, Vert, Orange) -> [|(Rouge, Jaune, Vert); (Rouge, Bleu, Jaune); (Rouge, Blanc, Bleu); (Rouge, Vert, Blanc); (Vert, Jaune, Orange); (Jaune, Bleu, Orange); (Bleu, Blanc, Orange); (Blanc, Vert, Orange)|]
  
  |_ -> failwith "Le cube rentre n'est pas valide"
  ;;


let trouve_sol_optimale cube=
  let l_formules = nettoie (creer_liste_formules 7) in
    let l_cubes1, l1 = tri_fusion (creer_liste_codes_cubes l_formules cube) l_formules in
      let l_cubes2, l2 = tri_fusion (creer_liste_codes_cubes l_formules (trouve_cube_fait cube)) l_formules in
        point_intersection l_cubes1 l1 l_cubes2 l2 [D;D;D;D;D;D;D;D;D;D;D;D;D;D;D] 15;;


(*Le programme résout tout pocket rubik cube optimalement en moins de 10 secondes*)

let cube = 
  [|(Orange, Blanc, Vert); 
  (Bleu, Orange, Jaune);  (**)
  (Orange, Bleu, Blanc); 
  (Jaune, Rouge, Bleu); 
  
  (Rouge, Vert, Blanc); 
  (Jaune, Orange, Vert); 
  (Bleu, Rouge, Blanc); 
  (Vert, Rouge, Jaune)|];;

trouve_sol_optimale cube;;

