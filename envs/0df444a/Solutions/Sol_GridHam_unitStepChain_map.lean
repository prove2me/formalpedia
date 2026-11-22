-- Prove2me | solution 1 for GridHam.unitStepChain_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:18:42.49454+00:00
-- url     : https://prove2.me/submissions/d3c2711c-4d03-4599-ad8f-e540f0aa8dd3

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → ℕ) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ w ∈ l, Adjacent v w → (f v + 1 = f w ∨ f w + 1 = f v)) →
    chainAdjacent l = true → unitStepChain (l.map f) = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro hstep hch
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
      have hA : unitStepB (f a) (f b) = true := by
        unfold unitStepB
        exact decide_eq_true (hstep a (by simp) b (by simp) hadj)
      have hB : unitStepChain ((b :: rest).map f) = true :=
        ih (fun v hv w hw =>
          hstep v (List.mem_cons.mpr (Or.inr hv)) w (List.mem_cons.mpr (Or.inr hw))) hcl
      have e : unitStepChain ((a :: b :: rest).map f) =
          (unitStepB (f a) (f b) && unitStepChain ((b :: rest).map f)) := rfl
      simp only [e, hA, hB, Bool.and_self]
end GridHam
