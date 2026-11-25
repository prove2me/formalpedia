-- Prove2me | solution 1 for Kyprianou.Ch04.bvNNRealFiniteAffineLeftCoercionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:35:50.619836+00:00
-- url     : https://prove2.me/submissions/7b8ab7d2-b573-4423-a332-ecd8ce07ae94

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I : Type} (τ : I → NNReal) (j : I → ℝ) (a c : ℝ)
    (S : Finset I) (u : NNReal) :
    a + c * (u : ℝ) + (∑ i ∈ S, if (τ i : ℝ) < (u : ℝ) then j i else 0) =
      a + c * (u : ℝ) + ∑ i ∈ S, if τ i < u then j i else 0 := by
  apply congrArg (fun z : ℝ => a + c*(u : ℝ) + z)
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : τ i < u
  · have hr : (τ i : ℝ) < (u : ℝ) := NNReal.coe_lt_coe.mpr h
    simp [h,hr]
  · have hr : ¬ (τ i : ℝ) < (u : ℝ) := fun hh => h (NNReal.coe_lt_coe.mp hh)
    simp [h,hr]
