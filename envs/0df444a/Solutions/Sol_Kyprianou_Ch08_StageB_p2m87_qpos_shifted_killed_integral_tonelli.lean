-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_shifted_killed_integral_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:05:22.325799+00:00
-- url     : https://prove2.me/submissions/13a30473-1b60-4161-b578-848608c5c8fc

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_shifted_integral_to_upper_event
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_upper_event_tonelli_source
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    let R : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
      if U ω < L ω then disc t *
        (if (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A then 1 else 0) else 0
    (∫⁻ ω, ∫⁻ s : ℝ≥0, R (τ ω + s) ω ∂positiveTimeLebesgue ∂P) =
      ∫⁻ t : ℝ≥0, disc t *
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
          shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue
:= by
  exact (p2m87_qpos_shifted_integral_to_upper_event X q a x A hA).trans
    (p2m87_qpos_upper_event_tonelli_source D X hpath q a x A hA)
