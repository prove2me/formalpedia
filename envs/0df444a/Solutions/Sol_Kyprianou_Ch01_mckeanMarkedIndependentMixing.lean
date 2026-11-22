-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanMarkedIndependentMixing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:11:58.860009+00:00
-- url     : https://prove2.me/submissions/00e9d4a3-c762-4b94-abb4-98d391e479c9

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_mckeanMarkedJointProductExpectation
import Theorems.Thm_Kyprianou_Ch01_mckeanMarkedDoubleIntegralMap
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ × Bool) (Z : Ω → ℝ)
    (f : ℝ → ℝ) (K : ℝ)
    (hT : Measurable T) (hZ : Measurable Z)
    (hf : Measurable f) (hBound : ∀ y, ‖f y‖ ≤ K)
    (hInd : IndepFun T Z P) :
    (∫ ω, if (T ω).2 = true then f ((T ω).1 + Z ω) else 0 ∂P) =
      (∫ ω, if (T ω).2 = true then
        (∫ ξ, f ((T ω).1 + Z ξ) ∂P) else 0 ∂P) := by
  let g : (ℝ × Bool) × ℝ → ℝ :=
    fun p => if p.1.2 = true then f (p.1.1 + p.2) else 0
  have hg : Measurable g := by
    have hTest :
        MeasurableSet {p : (ℝ × Bool) × ℝ | p.1.2 = true} :=
      measurable_fst.snd (measurableSet_singleton true)
    exact Measurable.ite hTest
      (hf.comp (measurable_fst.fst.add measurable_snd))
      measurable_const
  have hK : 0 ≤ K := (norm_nonneg (f 0)).trans (hBound 0)
  have hgBound (p : (ℝ × Bool) × ℝ) : ‖g p‖ ≤ K := by
    by_cases hp : p.1.2 = true
    · simpa [g, hp] using hBound (p.1.1 + p.2)
    · simp [g, hp, hK]
  have hJoint := Kyprianou.Ch01.mckeanMarkedJointProductExpectation
    P T Z g K hT hZ hg hgBound hInd
  have hMap := Kyprianou.Ch01.mckeanMarkedDoubleIntegralMap
    P T Z g hT hZ hg
  calc
    (∫ ω, if (T ω).2 = true then f ((T ω).1 + Z ω) else 0 ∂P)
        = ∫ ω, g (T ω, Z ω) ∂P := rfl
    _ = ∫ a, ∫ z, g (a, z) ∂P.map Z ∂P.map T := hJoint
    _ = ∫ ω, ∫ ξ, g (T ω, Z ξ) ∂P ∂P := hMap
    _ = ∫ ω, if (T ω).2 = true then
          (∫ ξ, f ((T ω).1 + Z ξ) ∂P) else 0 ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      by_cases h : (T ω).2 = true <;> simp [g, h]
