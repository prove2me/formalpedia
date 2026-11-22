-- Prove2me | solution 1 for GridHam.chain_detour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:37.537177+00:00
-- url     : https://prove2.me/submissions/0cb8153a-7696-4850-976e-8b652a1e9d94

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_chainAdjacent_reverse
public import Theorems.Thm_GridHam_chainAdjacent_cons
public import Theorems.Thm_GridHam_colSeg_head
public import Theorems.Thm_GridHam_colSeg_last
public import Theorems.Thm_GridHam_colSeg_chain
public import Theorems.Thm_P2M_GridHam_chainAdjacent_append__a723f1785ceb
public import Theorems.Thm_P2M_GridHam_head__append_of_head_13b1b2448961

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h y : ℕ) (hw : 1 ≤ w) (hy : y + 1 < h) (l2 : List Coord)
    (hb : chainAdjacent ((w - 1, y + 1) :: l2) = true) :
    chainAdjacent ((w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)) = true := by
  unfold rightDetour
  rw [List.append_assoc, List.append_assoc]
  have c3 : chainAdjacent (colSeg w (y + 1) (h - 1 - (y + 1)) ++ (w - 1, y + 1) :: l2) = true :=
    chainAdjacent_append' _ _ (w, y + 1) (w - 1, y + 1) (colSeg_last w (y + 1) _)
      (colSeg_chain _ _ _) rfl (by unfold Adjacent; dsimp only; omega) hb
  have c2 : chainAdjacent ((colSeg (w + 1) 0 (h - 1)).reverse ++
      (colSeg w (y + 1) (h - 1 - (y + 1)) ++ (w - 1, y + 1) :: l2)) = true :=
    chainAdjacent_append' _ _ (w + 1, 0 + (h - 1)) (w, y + 1 + (h - 1 - (y + 1)))
      (by simp [colSeg_head]) (chainAdjacent_reverse _ (colSeg_chain _ _ _))
      (head?_append_of_head _ _ _ (colSeg_head w (y + 1) _))
      (by unfold Adjacent; dsimp only; omega) c3
  have c1 : chainAdjacent (colSeg w 0 y ++ ((colSeg (w + 1) 0 (h - 1)).reverse ++
      (colSeg w (y + 1) (h - 1 - (y + 1)) ++ (w - 1, y + 1) :: l2))) = true :=
    chainAdjacent_append' _ _ (w, 0) (w + 1, 0) (colSeg_last w 0 y) (colSeg_chain _ _ _)
      (head?_append_of_head _ _ _ (by simp [colSeg_last]))
      (by unfold Adjacent; dsimp only; omega) c2
  exact chainAdjacent_cons _ (w, 0 + y) _ (head?_append_of_head _ _ _ (colSeg_head w 0 y))
    (by unfold Adjacent; dsimp only; omega) c1
end GridHam
