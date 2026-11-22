-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.kyprianou81_uncapped_ofReal_stopped_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T03:00:44.643824+00:00
-- url     : https://prove2.me/submissions/b29367ce-4160-4299-bf1a-695d8e90fccd

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_kyprianou81_capped_payoff_lintegral_isup
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_original_killedRecord_fixedFuture_markov_factor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ) (hr : Measurable reward) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let discountE : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (discount t)
    let rewardE : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f => ENNReal.ofReal (reward f)
    (∫⁻ ω, if U ω < L ω then discountE ((U ω).toNNReal) *
      rewardE (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
      else 0 ∂P) =
      (∫⁻ ω, if U ω < L ω then discountE ((U ω).toNNReal) else 0 ∂P) *
        (∫⁻ ω, rewardE (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  let U : Ω → ℝ≥0∞ := twoSidedExitUpTime X upper
  let L : Ω → ℝ≥0∞ := twoSidedExitDownTime X lower
  let discountE : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (discount t)
  let rewardE : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f => ENNReal.ofReal (reward f)
  have hdE : Measurable discountE := hd.ennreal_ofReal
  have hrE : Measurable rewardE := hr.ennreal_ofReal
  let A : ℕ → Set Ω := fun n => {ω | U ω < L ω} ∩ {ω | U ω ≤ (n : ℝ≥0∞)}
  let τ : ℕ → Ω → ℝ≥0 := fun n ω => (min (U ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
  let Fc : ℕ → Ω → ℝ≥0∞ := fun n ω => if ω ∈ A n then discountE (τ n ω) *
      rewardE (fun t : ℝ≥0 => X.X (τ n ω + t) ω - X.X (τ n ω) ω) else 0
  let Gc : ℕ → Ω → ℝ≥0∞ := fun n ω => if ω ∈ A n then discountE (τ n ω) else 0
  have hH1 := Kyprianou.Ch08.StageB.kyprianou81_capped_payoff_lintegral_isup X lower upper
    discountE hdE rewardE hrE
  have hPay : (∫⁻ ω, if U ω < L ω then discountE ((U ω).toNNReal) *
      rewardE (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
      else 0 ∂P) = ⨆ n, (∫⁻ ω, Fc n ω ∂P) := by
    simpa [Fc, A, τ, U, L] using hH1
  have hH1w := Kyprianou.Ch08.StageB.kyprianou81_capped_payoff_lintegral_isup X lower upper
    discountE hdE (fun _ => (1 : ℝ≥0∞)) measurable_const
  have hW : (∫⁻ ω, if U ω < L ω then discountE ((U ω).toNNReal) else 0 ∂P) =
      ⨆ n, (∫⁻ ω, Gc n ω ∂P) := by
    simpa [Gc, A, τ, U, L, mul_one] using hH1w
  have hEach (n : ℕ) : (∫⁻ ω, Fc n ω ∂P) =
      (∫⁻ ω, Gc n ω ∂P) * (∫⁻ ω, rewardE (fun t : ℝ≥0 => X.X t ω) ∂P) := by
    have h := avram_ws01h_original_killedRecord_fixedFuture_markov_factor X lower upper
      (n : ℝ≥0) discountE hdE rewardE hrE
    simpa [Fc, Gc, A, τ, U, L, ENNReal.coe_natCast] using h
  calc (∫⁻ ω, if U ω < L ω then discountE ((U ω).toNNReal) *
        rewardE (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
        else 0 ∂P)
      = ⨆ n, (∫⁻ ω, Fc n ω ∂P) := hPay
    _ = ⨆ n, (∫⁻ ω, Gc n ω ∂P) * (∫⁻ ω, rewardE (fun t : ℝ≥0 => X.X t ω) ∂P) := by
          congr 1
          funext n
          exact hEach n
    _ = (⨆ n, (∫⁻ ω, Gc n ω ∂P)) * (∫⁻ ω, rewardE (fun t : ℝ≥0 => X.X t ω) ∂P) := by
          rw [ENNReal.iSup_mul]
    _ = _ := by
          congr 1
          exact hW.symm
