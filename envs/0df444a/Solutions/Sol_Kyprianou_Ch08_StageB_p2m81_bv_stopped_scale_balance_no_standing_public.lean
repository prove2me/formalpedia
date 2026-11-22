-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_bv_stopped_scale_balance_no_standing_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T01:31:46.631803+00:00
-- url     : https://prove2.me/submissions/f224eb77-fee4-4380-a1ea-cb6d6f06ea6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_true_horizon_completed_survival_integral_balance_no_standing
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_horizon_split_rewards_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_stopped_horizon_components_le_scale_cap
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_uniform_nonnegative_bounded_integral_transfer
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : A.ψ φ = q)
    (W : ℝ → ℝ) (hW : AvramDividend.Classical.IsScaleFunction A q W)
    (hBV : A.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    AvramDividend.Classical.twoSidedExitExpectation A q a x *
        ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  letI : IsProbabilityMeasure P := A.isProbability
  let F_ : Ω → ℝ := fun ω => if twoSidedExitUpTime A (a-x) ω < twoSidedExitDownTime A (-x) ω then
    Real.exp (-(q * ((twoSidedExitUpTime A (a-x) ω).toNNReal : ℝ))) * W (x + A.X (twoSidedExitUpTime A (a-x) ω).toNNReal ω) else 0
  let S : ℕ → Ω → ℝ := fun n ω => let U : ℝ≥0∞ := twoSidedExitUpTime A (a-x) ω; let D : ℝ≥0∞ := twoSidedExitDownTime A (-x) ω;
    ((if U < D ∧ U.toNNReal ≤ (n : ℝ≥0) then Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + A.X U.toNNReal ω) else 0) +
    (if ((n : ℝ≥0) : ℝ≥0∞) < U ∧ ((n : ℝ≥0) : ℝ≥0∞) < D then Real.exp (-(q * (n : ℝ))) * W (x + A.X (n : ℝ≥0) ω) else 0))
  have hBalance (n : ℕ) : Integrable (S n) P ∧ (∫ ω, S n ω ∂P) = W x :=
    p2m81_bv_true_horizon_completed_survival_integral_balance_no_standing A q φ hq hφ hroot W hW hBV a x ha hx0 hxa (n : ℝ≥0)
  have hNonneg (n : ℕ) (ω : Ω) : 0 ≤ S n ω := (fun h => add_nonneg h.1 h.2) (avram_ws01b_true_horizon_split_rewards_nonnegative A q W hW a x ha hx0 hxa (n : ℝ≥0) ω)
  have hCap (n : ℕ) (ω : Ω) : S n ω ≤ W a := avram_ws01b_actual_stopped_horizon_components_le_scale_cap A q hq W hW a x ha hx0 hxa (n : ℝ≥0) ω
  have hConv : ∀ᵐ ω ∂P, Tendsto (fun n => S n ω) atTop (𝓝 (F_ ω)) :=
    Filter.Eventually.of_forall fun ω => avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal A q hq W hW a x ha hx0 hxa ω
  have hFVal : (∫ ω, F_ ω ∂P) = W x := tendsto_nhds_unique
    (avram_ws01b_uniform_nonnegative_bounded_integral_transfer S F_ (W a) (hW.2.1 a (le_of_lt ha)) (fun n => (hBalance n).1) hNonneg hCap hConv)
    (by rw [funext fun n => (hBalance n).2]; exact tendsto_const_nhds)
  have hFn : ∀ᵐ ω ∂P, ‖F_ ω‖ ≤ ‖W a‖ := hConv.mono fun ω hω => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hW.2.1 a (le_of_lt ha))] using le_of_tendsto hω.norm (Filter.Eventually.of_forall fun n => by simpa [Real.norm_eq_abs, abs_of_nonneg (hNonneg n ω)] using hCap n ω)
  have hFInt : Integrable F_ P := (integrable_const (W a)).mono
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hBalance n).1.aestronglyMeasurable) hConv) hFn
  have hFnn : ∀ᵐ ω ∂P, 0 ≤ F_ ω := hConv.mono fun ω hω =>
    ge_of_tendsto hω (Filter.Eventually.of_forall fun n => hNonneg n ω)
  have hAe : ∀ᵐ ω ∂P, (if twoSidedExitUpTime A (a-x) ω < twoSidedExitDownTime A (-x) ω then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime A (a-x) ω)))) * ENNReal.ofReal (W (x + A.X (twoSidedExitUpTime A (a-x) ω).toNNReal ω)) else 0)
      = ENNReal.ofReal (F_ ω) := Filter.Eventually.of_forall fun ω => by
      by_cases hu : twoSidedExitUpTime A (a-x) ω < twoSidedExitDownTime A (-x) ω
      · simp only [F_, if_pos hu]
        rw [ENNReal.coe_toNNReal_eq_toReal]
        exact (ENNReal.ofReal_mul (Real.exp_nonneg _)).symm
      · simp [F_, hu]
  have hTerminal : (∫⁻ ω, if twoSidedExitUpTime A (a-x) ω < twoSidedExitDownTime A (-x) ω then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime A (a-x) ω)))) * ENNReal.ofReal (W (x + A.X (twoSidedExitUpTime A (a-x) ω).toNNReal ω)) else 0 ∂P) = ENNReal.ofReal (W x) :=
    (lintegral_congr_ae hAe).trans (by
      have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFInt hFnn
      rw [hFVal] at h; exact h.symm)
  simpa only [twoSidedExitExpectation] using (chat04_strict_stopped_exit_payoff_any_measure_factorisation A P q a x hxa W).symm.trans hTerminal
