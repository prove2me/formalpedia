-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_factor_enreal_stopped_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:31:12.150575+00:00
-- url     : https://prove2.me/submissions/b844e2e9-1203-4fc1-b07d-6820996e158d

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_kyprianou81_capped_payoff_lintegral_isup
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_original_killedRecord_fixedFuture_markov_factor
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (lower upper : ℝ) (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    (∫⁻ ω, if U ω < L ω then discount ((U ω).toNNReal) *
        reward (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
      else 0 ∂P) =
      (∫⁻ ω, if U ω < L ω then discount ((U ω).toNNReal) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)
:= by
  have hite (p : Prop) (d : Decidable p) (a b : ℝ≥0∞) :
      @ite ℝ≥0∞ p d a b = @ite ℝ≥0∞ p (Classical.propDecidable p) a b := by
    rw [Subsingleton.elim d (Classical.propDecidable p)]
  let U : Ω → ℝ≥0∞ := twoSidedExitUpTime X upper
  let L : Ω → ℝ≥0∞ := twoSidedExitDownTime X lower
  let A : ℕ → Set Ω := fun n => {ω | U ω < L ω} ∩ {ω | U ω ≤ (n : ℝ≥0∞)}
  let τ : ℕ → Ω → ℝ≥0 := fun n ω => (min (U ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
  let Fc : ℕ → Ω → ℝ≥0∞ := fun n ω => if ω ∈ A n then discount (τ n ω) *
      reward (fun t : ℝ≥0 => X.X (τ n ω + t) ω - X.X (τ n ω) ω) else 0
  let Gc : ℕ → Ω → ℝ≥0∞ := fun n ω => if ω ∈ A n then discount (τ n ω) else 0
  have hH1 := Kyprianou.Ch08.StageB.kyprianou81_capped_payoff_lintegral_isup X lower upper
    discount hd reward hr
  have hPay : (∫⁻ ω, if U ω < L ω then discount ((U ω).toNNReal) *
      reward (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
      else 0 ∂P) = ⨆ n, (∫⁻ ω, Fc n ω ∂P) := by
    simpa [Fc, A, τ, U, L, hite] using hH1
  have hH1w := Kyprianou.Ch08.StageB.kyprianou81_capped_payoff_lintegral_isup X lower upper
    discount hd (fun _ => (1 : ℝ≥0∞)) measurable_const
  have hW : (∫⁻ ω, if U ω < L ω then discount ((U ω).toNNReal) else 0 ∂P) =
      ⨆ n, (∫⁻ ω, Gc n ω ∂P) := by
    simpa [Gc, A, τ, U, L, mul_one, hite] using hH1w
  have hEach (n : ℕ) : (∫⁻ ω, Fc n ω ∂P) =
      (∫⁻ ω, Gc n ω ∂P) * (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
    have h := avram_ws01h_original_killedRecord_fixedFuture_markov_factor X lower upper
      (n : ℝ≥0) discount hd reward hr
    simpa [Fc, Gc, A, τ, U, L, ENNReal.coe_natCast, hite] using h
  calc (∫⁻ ω, if U ω < L ω then discount ((U ω).toNNReal) *
        reward (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω)
        else 0 ∂P)
      = ⨆ n, (∫⁻ ω, Fc n ω ∂P) := hPay
    _ = ⨆ n, (∫⁻ ω, Gc n ω ∂P) * (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
          congr 1
          funext n
          exact hEach n
    _ = (⨆ n, (∫⁻ ω, Gc n ω ∂P)) * (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
          rw [ENNReal.iSup_mul]
    _ = _ := by
          congr 1
          exact hW.symm
