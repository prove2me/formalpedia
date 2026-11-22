-- Prove2me | solution 1 for GridHam.chainAdjacent_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:55:38.237363+00:00
-- url     : https://prove2.me/submissions/87b502a0-8e43-42d2-90fc-d1fae649db38

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_chainAdjacent_append
public import Theorems.Thm_GridHam_adjacent_symm

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l : List Coord),
    chainAdjacent l = true → chainAdjacent l.reverse = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro hch
    cases l with
    | nil => rfl
    | cons b rest =>
      have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
        simpa [chainAdjacent] using hch
      simp at hc'
      obtain ⟨hab, hcl⟩ := hc'
      have hadj : Adjacent a b := by
        unfold adjacentB at hab
        by_contra hcon
        simp [hcon] at hab
      rw [List.reverse_cons]
      exact chainAdjacent_append (b :: rest).reverse a [] b (by simp) (ih hcl)
        (adjacent_symm hadj) rfl
end GridHam
