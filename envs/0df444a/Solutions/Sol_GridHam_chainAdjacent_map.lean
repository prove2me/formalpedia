-- Prove2me | solution 1 for GridHam.chainAdjacent_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:21:46.161633+00:00
-- url     : https://prove2.me/submissions/d14a9b50-55b0-49d3-934e-6b4d3f2e6dd8

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → Coord) (hf : ∀ v w, Adjacent v w → Adjacent (f v) (f w)) :
    ∀ (l : List Coord), chainAdjacent l = true → chainAdjacent (l.map f) = true := by
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
      have hA : adjacentB (f a) (f b) = true := by
        unfold adjacentB
        exact decide_eq_true (hf a b hadj)
      have hB : chainAdjacent ((b :: rest).map f) = true := ih hcl
      have e : chainAdjacent ((a :: b :: rest).map f) =
          (adjacentB (f a) (f b) && chainAdjacent ((b :: rest).map f)) := rfl
      simp only [e, hA, hB, Bool.and_self]
end GridHam
