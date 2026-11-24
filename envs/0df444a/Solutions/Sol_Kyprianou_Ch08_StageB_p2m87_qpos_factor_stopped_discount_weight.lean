-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_factor_stopped_discount_weight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T05:25:41.690805+00:00
-- url     : https://prove2.me/submissions/0aa7a206-27b6-4fd4-b6d3-54acbb956a99

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_payoff_bridge_public
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a x : ℝ) (hq : 0 < q) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    (∫⁻ ω, if U ω < L ω then disc ((U ω).toNNReal) else 0 ∂P) =
      ENNReal.ofReal (upBeforeDownExpectation P D.X q x a) := by
  dsimp only
  let U : Ω → ℝ≥0∞ := twoSidedExitUpTime X (a - x)
  let L : Ω → ℝ≥0∞ := twoSidedExitDownTime X (-x)
  let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
  change
    (∫⁻ ω, if U ω < L ω then disc ((U ω).toNNReal) else 0 ∂P) =
      ENNReal.ofReal (upBeforeDownExpectation P D.X q x a)
  let Wlin : ℝ≥0∞ := ∫⁻ ω, if U ω < L ω then disc ((U ω).toNNReal) else 0 ∂P
  have hdisc (t : ℝ≥0) : disc t ≤ 1 := by
    have harg : -q * (t : ℝ) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) (NNReal.coe_nonneg t)
    exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr harg)
  have hWle : Wlin ≤ 1 := by
    calc
      Wlin ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P := by
        apply lintegral_mono
        intro ω
        by_cases hUL : U ω < L ω <;> simp [Wlin, hUL, hdisc]
      _ = 1 := by simp
  have hWne : Wlin ≠ ∞ := (lt_of_le_of_lt hWle (by simp)).ne
  have htwo : twoSidedExitExpectation X q a x = Wlin := by
    unfold twoSidedExitExpectation
    apply lintegral_congr
    intro ω
    dsimp [U, L, disc, Wlin]
    by_cases hUL : twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω
    · have hexp :
          -(q * (twoSidedExitUpTime X (a - x) ω).toReal) =
            -q * ((twoSidedExitUpTime X (a - x) ω).toNNReal : ℝ) := by
        rw [ENNReal.coe_toNNReal_eq_toReal]
        ring
      simp [hUL, hexp]
    · simp [hUL]
  have hbridge := source_result81_upper_payoff_bridge_public D X hpath q x a
  change Wlin = ENNReal.ofReal (upBeforeDownExpectation P D.X q x a)
  rw [hbridge, htwo]
  exact (ENNReal.ofReal_toReal hWne).symm
