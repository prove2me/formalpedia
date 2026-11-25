-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzOneJumpLedgerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:32:56.212599+00:00
-- url     : https://prove2.me/submissions/a83e3aa5-cc76-4992-b317-4525b5d785ed

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineSegmentChainV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c j κ T : ℝ) (hκ0 : 0 ≤ κ) (hκT : κ ≤ T)
    (hNonneg : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ U s)
    (hPositive : ∀ s ∈ Set.Ioc (0 : ℝ) T, 0 < U s) :
    f (U T, a + j + c * T) =
      f (U 0, a) +
      (∫ s in 0..κ, fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
         c * fderiv ℝ f (U s, a + c * s) (0, 1)) +
      (f (U κ, a + j + c * κ) - f (U κ, a + c * κ)) +
      (∫ s in κ..T, fderiv ℝ f (U s, a + j + c * s) (1, 0) * deriv U s +
         c * fderiv ℝ f (U s, a + j + c * s) (0, 1)) := by
  have hLnon : ∀ s ∈ Set.Icc (0 : ℝ) κ, 0 ≤ U s := by
    intro s hs
    exact hNonneg s ⟨hs.1, hs.2.trans hκT⟩
  have hRnon : ∀ s ∈ Set.Icc κ T, 0 ≤ U s := by
    intro s hs
    exact hNonneg s ⟨hκ0.trans hs.1, hs.2⟩
  have hLpos : ∀ s ∈ Set.Ioc (0 : ℝ) κ, 0 < U s := by
    intro s hs
    exact hPositive s ⟨hs.1, hs.2.trans hκT⟩
  have hRpos : ∀ s ∈ Set.Ioc κ T, 0 < U s := by
    intro s hs
    exact hPositive s ⟨lt_of_le_of_lt hκ0 hs.1, hs.2⟩
  have hL := Kyprianou.Ch04.exercise42LipschitzAffineSegmentChainV1
    f hf U K hU a c 0 κ hκ0 hLnon hLpos
  have hR := Kyprianou.Ch04.exercise42LipschitzAffineSegmentChainV1
    f hf U K hU (a + j) c κ T hκT hRnon hRpos
  simp only [mul_zero, add_zero] at hL
  linarith