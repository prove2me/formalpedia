-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_upper_exit_markov_occupation_factor_le_v2_no_scale_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T04:40:42.129795+00:00
-- url     : https://prove2.me/submissions/a2b005b8-6a07-404a-a7cd-7d608f5876c8

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_measurable_reward
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_enreal_stopped_reward_factor
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_halfline_reward_expectation
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_stopped_payoff_occupation
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_stopped_discount_weight
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        (∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X x) 0 ω ∧
              tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
        ENNReal.ofReal (upBeforeDownExpectation P D.X q x a) *
          (∫⁻ t : ℝ≥0,
            ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
              P {ω | (t : WithTop ℝ≥0) <
                tauMinus (shifted D.X a) 0 ω ∧
                shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue) := by
  intro Ω mΩ P hP D ψ hψ q a x hq ha hx hxa A hA
  obtain ⟨F, X, hpath, _⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  let U : Ω → ℝ≥0∞ := twoSidedExitUpTime X (a - x)
  let L : Ω → ℝ≥0∞ := twoSidedExitDownTime X (-x)
  let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
  let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
  have hdisc : Measurable disc := by
    dsimp [disc]
    fun_prop
  obtain ⟨reward, hreward, hreward_value⟩ :=
    p2m87_qpos_factor_measurable_reward q a ha A hA
  have hfactor :=
    p2m87_qpos_factor_enreal_stopped_reward_factor X (-x) (a - x) disc hdisc reward hreward
  have hstop :=
    p2m87_qpos_factor_stopped_payoff_occupation D X hpath q a x hq ha hx hxa
      A hA reward hreward hreward_value
  have hweight :=
    p2m87_qpos_factor_stopped_discount_weight D ψ hψ X hpath q a x hq ha hx hxa
  have hweight' :
      (∫⁻ ω, if U ω < L ω then disc ((U ω).toNNReal) else 0 ∂P) =
        ENNReal.ofReal (upBeforeDownExpectation P D.X q x a) := by
    simpa only [U, L, disc] using hweight
  have hfuture :=
    p2m87_qpos_factor_halfline_reward_expectation D X hpath q a A hA
      reward hreward hreward_value
  calc
    (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
          shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
        ∫⁻ ω, if U ω < L ω then disc (τ ω) *
          reward (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P := by
      simpa only [U, L, τ, disc] using hstop.symm
    _ = (∫⁻ ω, if U ω < L ω then disc ((U ω).toNNReal) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
      simpa only [τ, U, L] using hfactor
    _ = ENNReal.ofReal (upBeforeDownExpectation P D.X q x a) *
        (∫⁻ t : ℝ≥0, disc t *
          P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X a) 0 ω ∧
            shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue) := by
      rw [hweight', hfuture]
    _ = ENNReal.ofReal (upBeforeDownExpectation P D.X q x a) *
        (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X a) 0 ω ∧
            shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue) := by
      simp only [disc]
