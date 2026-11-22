-- Prove2me | solution 1 for GridHam.chainAdjacent_map_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:23.333708+00:00
-- url     : https://prove2.me/submissions/95f2689a-ad2f-4559-a572-e8674a534c37

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → Coord) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ u ∈ l, Adjacent v u → Adjacent (f v) (f u)) →
    chainAdjacent l = true → chainAdjacent (l.map f) = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro hf hch
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
        exact decide_eq_true (hf a (by simp) b (by simp) hadj)
      have hB : chainAdjacent ((b :: rest).map f) = true :=
        ih (fun v hv u hu =>
          hf v (List.mem_cons.mpr (Or.inr hv)) u (List.mem_cons.mpr (Or.inr hu))) hcl
      have e : chainAdjacent ((a :: b :: rest).map f) =
          (adjacentB (f a) (f b) && chainAdjacent ((b :: rest).map f)) := rfl
      simp only [e, hA, hB, Bool.and_self]
end GridHam
