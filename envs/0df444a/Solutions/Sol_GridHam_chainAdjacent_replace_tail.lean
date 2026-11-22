-- Prove2me | solution 1 for GridHam.chainAdjacent_replace_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:54:49.583633+00:00
-- url     : https://prove2.me/submissions/a14c018b-ab48-4cb3-ba3e-18280963319b

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_chainAdjacent_cons

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l1 : List Coord) (a : Coord) (m m' : List Coord),
    chainAdjacent (l1 ++ a :: m) = true → chainAdjacent (a :: m') = true →
    chainAdjacent (l1 ++ a :: m') = true := by
  intro l1
  induction l1 with
  | nil => intro a m m' _ h2; exact h2
  | cons x l ih =>
    intro a m m' h1 h2
    cases l with
    | nil =>
      have hc' : (adjacentB x a && chainAdjacent (a :: m)) = true := by
        simpa [chainAdjacent] using h1
      simp at hc'
      obtain ⟨hxa, _⟩ := hc'
      have hadj : Adjacent x a := by
        unfold adjacentB at hxa
        by_contra hcon
        simp [hcon] at hxa
      exact chainAdjacent_cons x a (a :: m') rfl hadj h2
    | cons z l' =>
      have hc' : (adjacentB x z && chainAdjacent (z :: (l' ++ a :: m))) = true := by
        simpa [chainAdjacent] using h1
      simp at hc'
      obtain ⟨hxz, hcl⟩ := hc'
      have hadj : Adjacent x z := by
        unfold adjacentB at hxz
        by_contra hcon
        simp [hcon] at hxz
      have hrec := ih a m m' hcl h2
      exact chainAdjacent_cons x z _ rfl hadj hrec
end GridHam
