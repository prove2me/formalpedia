-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.monotoneNullMeasurableSetIntegralLeftLimit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:55:07.719705+00:00
-- url     : https://prove2.me/submissions/408a85ed-dbce-4e4c-90af-08b4008c1009
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_Kyprianou_Ch08_StageB_rationalLowerMeasurableEnvelopeExists
import Theorems.Thm_Kyprianou_Ch08_StageB_rationalLowerEnvelopeIntegralEq
import Theorems.Thm_Kyprianou_Ch08_StageB_monotoneSetIntegralLeftLimitFromAEMargin
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ) (A : ℝ → Set Ω)
    (hMeas : ∀ h : ℝ, NullMeasurableSet (A h) P)
    (hMono : Monotone A)
    (hInt : Integrable g P)
    (hMargin : ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → ω ∈ A y →
        ∃ h : ℝ, h < y ∧ ω ∈ A h) :
    ∀ y : ℝ,
      Tendsto (fun h : ℝ => (∫ ω in A h, g ω ∂P))
        (nhdsWithin y (Set.Iio y))
        (nhds (∫ ω in A y, g ω ∂P)) := by
  obtain ⟨B, hBMeas, hBMono, hBMargin, hBDef⟩ :=
    Kyprianou.Ch08.StageB.rationalLowerMeasurableEnvelopeExists P A
  have hMarginB : ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → ω ∈ B y →
        ∃ h : ℝ, h < y ∧ ω ∈ B h := by
    intro y
    exact Filter.Eventually.of_forall (fun ω _ => hBMargin y ω)
  have hEq :=
    Kyprianou.Ch08.StageB.rationalLowerEnvelopeIntegralEq
      P g A B hMeas hMono hMargin hBMeas hBDef
  have hLimit :=
    Kyprianou.Ch08.StageB.monotoneSetIntegralLeftLimitFromAEMargin
      P g B hBMeas hBMono hInt hMarginB
  intro y
  have hFun :
      (fun h : ℝ => (∫ ω in B h, g ω ∂P)) =
      (fun h : ℝ => (∫ ω in A h, g ω ∂P)) := by
    funext h
    exact hEq h
  simpa only [hFun, hEq y] using hLimit y
