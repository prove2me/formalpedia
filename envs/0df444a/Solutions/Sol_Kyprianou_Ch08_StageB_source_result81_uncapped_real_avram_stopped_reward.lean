-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_uncapped_real_avram_stopped_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T04:37:36.865801+00:00
-- url     : https://prove2.me/submissions/a9345d91-5c35-44f6-ab14-b0057920767c

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_kyprianou81_uncapped_ofReal_stopped_reward_factor
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_uncapped_real_avram_stopped_reward_integrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (hd : Measurable discount) (hdb : ∀ t, 0 ≤ discount t ∧ discount t ≤ 1)
    (reward : (ℝ≥0 → ℝ) → ℝ) (hr : Measurable reward) (hrb : ∀ f, 0 ≤ reward f ∧ reward f ≤ 1) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let weight := fun ω => if U ω < L ω then discount (U ω).toNNReal else 0
    let payoff := fun ω => if U ω < L ω then
      discount (U ω).toNNReal *
        reward (fun s => X.X ((U ω).toNNReal + s) ω - X.X (U ω).toNNReal ω)
      else 0
    Integrable payoff P ∧
      (∫ ω, payoff ω ∂P) = (∫ ω, weight ω ∂P) * (∫ ω, reward (fun s => X.X s ω) ∂P) := by
  classical
  let U : Ω → ℝ≥0∞ := twoSidedExitUpTime X upper
  let L : Ω → ℝ≥0∞ := twoSidedExitDownTime X lower
  let τU : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
  let shiftPath : Ω → (ℝ≥0 → ℝ) := fun ω s => X.X (τU ω + s) ω - X.X (τU ω) ω
  let origPath : Ω → (ℝ≥0 → ℝ) := fun ω s => X.X s ω
  let weightR : Ω → ℝ := fun ω => if U ω < L ω then discount (τU ω) else 0
  let payoffR : Ω → ℝ := fun ω => if U ω < L ω then discount (τU ω) * reward (shiftPath ω) else 0
  let origR : Ω → ℝ := fun ω => reward (origPath ω)
  have hChild : Integrable payoffR P ∧ Integrable weightR P ∧ Integrable origR P := Kyprianou.Ch08.StageB.source_result81_uncapped_real_avram_stopped_reward_integrable X lower upper discount hd hdb reward hr hrb
  have hNN : (∀ ω, 0 ≤ payoffR ω) ∧ (∀ ω, 0 ≤ weightR ω) ∧ (∀ ω, 0 ≤ origR ω) := ⟨fun ω => by simp only [payoffR]; split_ifs with h; exacts [mul_nonneg (hdb _).1 (hrb _).1, le_rfl], fun ω => by simp only [weightR]; split_ifs with h; exacts [(hdb _).1, le_rfl], fun ω => (hrb _).1⟩
  have hOf : (∀ ω, ENNReal.ofReal (payoffR ω) = (if U ω < L ω then ENNReal.ofReal (discount (τU ω)) * ENNReal.ofReal (reward (shiftPath ω)) else 0)) ∧ (∀ ω, ENNReal.ofReal (weightR ω) = (if U ω < L ω then ENNReal.ofReal (discount (τU ω)) else 0)) := ⟨fun ω => by simp only [payoffR]; split_ifs with h; exacts [ENNReal.ofReal_mul (hdb (τU ω)).1, by simp], fun ω => by simp only [weightR]; split_ifs with h; exacts [rfl, by simp]⟩
  have hH2E : (∫⁻ ω, (if U ω < L ω then ENNReal.ofReal (discount (τU ω)) * ENNReal.ofReal (reward (shiftPath ω)) else 0) ∂P) = (∫⁻ ω, (if U ω < L ω then ENNReal.ofReal (discount (τU ω)) else 0) ∂P) * (∫⁻ ω, ENNReal.ofReal (reward (origPath ω)) ∂P) := Kyprianou.Ch08.StageB.kyprianou81_uncapped_ofReal_stopped_reward_factor X lower upper discount hd reward hr
  have hOfEq : ENNReal.ofReal (∫ ω, payoffR ω ∂P) = ENNReal.ofReal ((∫ ω, weightR ω ∂P) * (∫ ω, origR ω ∂P)) := by
    have e1 := ofReal_integral_eq_lintegral_ofReal hChild.1 (Filter.Eventually.of_forall hNN.1)
    have e2 := ofReal_integral_eq_lintegral_ofReal hChild.2.1 (Filter.Eventually.of_forall hNN.2.1)
    have e3 := ofReal_integral_eq_lintegral_ofReal hChild.2.2 (Filter.Eventually.of_forall hNN.2.2)
    rw [lintegral_congr hOf.1] at e1
    rw [lintegral_congr hOf.2] at e2
    have e3u : ENNReal.ofReal (∫ ω, origR ω ∂P) = ∫⁻ ω, ENNReal.ofReal (reward (origPath ω)) ∂P := e3
    rw [e1, hH2E, ← e2, ← e3u]
    exact (ENNReal.ofReal_mul (integral_nonneg_of_ae (Filter.Eventually.of_forall hNN.2.1))).symm
  have hRealEq : (∫ ω, payoffR ω ∂P) = (∫ ω, weightR ω ∂P) * (∫ ω, origR ω ∂P) := by
    have h1 := congrArg ENNReal.toReal hOfEq
    rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae (Filter.Eventually.of_forall hNN.1)), ENNReal.toReal_ofReal (mul_nonneg (integral_nonneg_of_ae (Filter.Eventually.of_forall hNN.2.1)) (integral_nonneg_of_ae (Filter.Eventually.of_forall hNN.2.2)))] at h1
    exact h1
  exact ⟨hChild.1, hRealEq⟩
