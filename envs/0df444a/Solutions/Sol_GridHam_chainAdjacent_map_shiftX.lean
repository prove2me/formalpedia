-- Prove2me | solution 1 for GridHam.chainAdjacent_map_shiftX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:23:34.523887+00:00
-- url     : https://prove2.me/submissions/441a1b0a-8992-4539-bcf5-c67d751f90a8

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_adjacent_shiftX

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (d : ℕ) : ∀ (l : List Coord),
    chainAdjacent l = true → chainAdjacent (l.map (shiftX d)) = true := by
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
      have hA : adjacentB (shiftX d a) (shiftX d b) = true := by
        unfold adjacentB
        exact decide_eq_true (adjacent_shiftX d hadj)
      have hB : chainAdjacent ((b :: rest).map (shiftX d)) = true := ih hcl
      have e : chainAdjacent ((a :: b :: rest).map (shiftX d)) =
          (adjacentB (shiftX d a) (shiftX d b) && chainAdjacent ((b :: rest).map (shiftX d))) :=
        rfl
      simp only [e, hA, hB, Bool.and_self]
end GridHam
