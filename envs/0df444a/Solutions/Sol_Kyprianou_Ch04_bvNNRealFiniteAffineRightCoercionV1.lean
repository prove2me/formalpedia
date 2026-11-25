-- Prove2me | solution 1 for Kyprianou.Ch04.bvNNRealFiniteAffineRightCoercionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:35:50.511433+00:00
-- url     : https://prove2.me/submissions/2d0937b1-f276-4624-94ec-d755bb232896

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I : Type} (τ : I → NNReal) (j : I → ℝ) (a c : ℝ)
    (S : Finset I) (u : ℝ) (hu : 0 ≤ u) :
    a + c * u + (∑ i ∈ S, if (τ i : ℝ) ≤ u then j i else 0) =
      a + c * (Real.toNNReal u : ℝ) +
        ∑ i ∈ S, if τ i ≤ Real.toNNReal u then j i else 0 := by
  rw [Real.coe_toNNReal u hu]
  apply congrArg (fun z : ℝ => a + c*u + z)
  apply Finset.sum_congr rfl
  intro i hi
  have h : (τ i : ℝ) ≤ u ↔ τ i ≤ Real.toNNReal u := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal u hu]
  by_cases h' : (τ i : ℝ) ≤ u
  · simp [h', h.mp h']
  · have hn : ¬ τ i ≤ Real.toNNReal u := fun hh => h' (h.mpr hh)
    simp [h',hn]
