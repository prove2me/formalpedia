-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:24:28.684565+00:00
-- url     : https://prove2.me/submissions/41dce315-01b1-4147-bbde-f194edcda4d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
import Theorems.Thm_GlobalTheory_LipschitzTR_norm_lipschitzOneVariableKernel_le
import Theorems.Thm_GlobalTheory_LipschitzTR_abs_pow_mul_exp_le
import Theorems.Thm_GlobalTheory_LipschitzTR_continuous_lipschitzOneVariableKernel
import Theorems.Thm_GlobalTheory_LipschitzTR_norm_le_sum_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (F : Type) [Field F] [NumberField F] (k : ℕ) (hk : 2 ≤ k)
    (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by
  refine ⟨?_, fun b => ?_⟩
  · unfold Phi
    exact continuous_finset_prod _ fun τ _ =>
      (continuous_lipschitzOneVariableKernel hk (hz τ)).comp ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ τ, c ≤ 2 * Real.pi * |(z τ).im| / 2 := by
    rcases isEmpty_or_nonempty (F →+* ℝ) with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ0, hτ0⟩ := Finite.exists_min (fun τ => 2 * Real.pi * |(z τ).im| / 2)
      exact ⟨_, by have := abs_pos.2 (hz τ0); positivity, hτ0⟩
  set K : ℝ := ∏ τ, (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) with hK
  have hbound : ∀ v : RSp F, ‖Phi k z v‖ ≤ K * Real.exp (-c * ‖v‖) := by
    intro v
    have hfac : ∀ τ, ‖phi1 k (z τ) (v τ)‖ ≤
        (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|) := by
      intro τ
      have ha : 0 < 2 * Real.pi * |(z τ).im| := by have := abs_pos.2 (hz τ); positivity
      refine (norm_lipschitzOneVariableKernel_le k (z τ) (v τ)).trans ((abs_pow_mul_exp_le (k - 1) ha (v τ)).trans ?_)
      gcongr
      have := hcle τ
      nlinarith [abs_nonneg (v τ)]
    calc ‖Phi k z v‖ = ∏ τ, ‖phi1 k (z τ) (v τ)‖ := by unfold Phi; rw [norm_prod]
      _ ≤ ∏ τ, ((((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|)) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => hfac τ
      _ = K * Real.exp (-c * ∑ τ, |v τ|) := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
      _ ≤ K * Real.exp (-c * ‖v‖) := by
        have hK0 : 0 ≤ K := Finset.prod_nonneg fun τ _ => by positivity
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [norm_le_sum_abs v])) hK0
  have h1 : Phi k z =O[Filter.cocompact (RSp F)] fun v : RSp F => Real.exp (-c * ‖v‖) :=
    Asymptotics.IsBigO.of_bound K (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hbound v)
  have h2 : (fun v : RSp F => Real.exp (-c * ‖v‖)) =O[Filter.cocompact (RSp F)]
      fun v : RSp F => ‖v‖ ^ (-b) :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-b)).isBigO.comp_tendsto tendsto_norm_cocompact_atTop
  exact h1.trans h2
end GlobalTheory.LipschitzTR
