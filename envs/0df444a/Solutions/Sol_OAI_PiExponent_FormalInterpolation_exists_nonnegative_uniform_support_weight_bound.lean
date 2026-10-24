-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_nonnegative_uniform_support_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:36:48.938279+00:00
-- url     : https://prove2.me/submissions/c33c3ac3-2783-4e77-9d54-5621916af324

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d t : Nat} (w : Fin d → Rat)
    (b : Fin t → MvPolynomial (Fin d) Complex) :
    ∃ C : Real, 0 ≤ C ∧ ∀ i, ∀ a ∈ (b i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ C := by
  classical
  let S : Finset (Fin d →₀ Nat) :=
    Finset.univ.biUnion fun i : Fin t => (b i).support
  let f : (Fin d →₀ Nat) → Real := fun a =>
    ∑ k, (w k : Real) * (a k : Real)
  let V : Finset Real := S.image f
  let C : Real := max 0 (if h : V.Nonempty then V.max' h else 0)
  refine ⟨C, ?_, ?_⟩
  · simp [C]
  · intro i a ha
    have haS : a ∈ S := by
      simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, ha⟩
    have hV : f a ∈ V := Finset.mem_image.mpr ⟨a, haS, rfl⟩
    have hne : V.Nonempty := ⟨f a, hV⟩
    change f a ≤ max 0 (if h : V.Nonempty then V.max' h else 0)
    rw [dif_pos hne]
    exact le_max_of_le_right (Finset.le_max' V (f a) hV)