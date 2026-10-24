-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_support_sum_mul_of_support_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:55:44.291353+00:00
-- url     : https://prove2.me/submissions/f1c6c61e-7903-4326-b0af-f0584f59afe6

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators Pointwise
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d t : Nat} (w : Fin d → Rat)
    (p q : Fin t → MvPolynomial (Fin d) Complex) (A B : Real)
    (hp : ∀ i, ∀ a ∈ (p i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ A)
    (hq : ∀ i, ∀ a ∈ (q i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ B) :
    ∀ a ∈ (∑ i : Fin t, p i * q i).support,
      ∑ k, (w k : Real) * (a k : Real) ≤ A + B := by
  classical
  intro a ha
  have hmem : a ∈ (Finset.univ : Finset (Fin t)).biUnion
      (fun i => (p i * q i).support) := by
    exact MvPolynomial.support_sum (s := Finset.univ)
      (f := fun i => p i * q i) ha
  obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp hmem
  have hprod : a ∈ (p i).support + (q i).support :=
    MvPolynomial.support_mul (p i) (q i) hai
  obtain ⟨b, hb, c, hc, hac⟩ := Finset.mem_add.mp hprod
  have hpb := hp i b hb
  have hqc := hq i c hc
  rw [← hac]
  simp only [Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  exact add_le_add hpb hqc
