-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_tail_integral_core_left_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:41:11.755923+00:00
-- url     : https://prove2.me/submissions/a9a83bb2-c99d-4913-9303-4fa087fb0293
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Topology.Order.LeftRight
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_bounds
import Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightIntegralMonotoneAndLimits
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    (∀ h : ℝ, 0 < h → 0 < (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q *
      1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) ∧
    MonotoneOn (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1)
      * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Ioi 0) ∧
    (∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1
      h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Iic h₀) h₀) ∧
    Tendsto (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) *
      discountedAt q (tauPlus D.X 1 ω) ∂P)) atTop (nhds 1) ∧
    (∀ y : ℝ, 0 < y → Tendsto (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
      Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (nhdsWithin y (Set.Iio y))
      (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω}, Real.exp (Phi ψ q * 1) *
      discountedAt q (tauPlus D.X 1 ω) ∂P))) := by
  obtain ⟨hmono, htop, hleft⟩ :=
    Kyprianou.Ch08.StageB.actualHeightIntegralMonotoneAndLimits
      P D ψ W hψ hW q hq
  refine ⟨?_, hmono, ?_, htop, hleft⟩
  · intro h hh
    exact (Kyprianou.Ch08.StageB.actual_height_tail_bounds
      P D ψ W hψ hW q hq h hh).1
  · intro h hh
    exact (continuousWithinAt_Iio_iff_Iic).mp (hleft h hh)
