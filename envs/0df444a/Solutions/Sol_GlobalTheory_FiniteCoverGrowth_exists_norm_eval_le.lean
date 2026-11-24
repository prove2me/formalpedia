-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.exists_norm_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:07:54.985558+00:00
-- url     : https://prove2.me/submissions/021eb4d7-fc94-46df-86ef-56c79aec33c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution {d : ℕ} (c : MvPolynomial (Fin d) ℂ) :
    ∃ (K : ℝ) (M : ℕ), 0 ≤ K ∧ ∀ x : Fin d → ℂ, ‖MvPolynomial.eval x c‖ ≤ K * (1 + ‖x‖) ^ M := by
  induction c using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp⟩
  | add p q hp hq =>
    obtain ⟨K, M, hK, h⟩ := hp
    obtain ⟨K', M', hK', h'⟩ := hq
    refine ⟨K + K', M + M', by positivity, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : (1 + ‖x‖) ^ M ≤ (1 + ‖x‖) ^ (M + M') := pow_le_pow_right₀ h1 (by omega)
    have h3 : (1 + ‖x‖) ^ M' ≤ (1 + ‖x‖) ^ (M + M') := pow_le_pow_right₀ h1 (by omega)
    rw [map_add]
    refine (norm_add_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left h2 hK
    have := mul_le_mul_of_nonneg_left h3 hK'
    nlinarith [h x, h' x]
  | mul_X p i hp =>
    obtain ⟨K, M, hK, h⟩ := hp
    refine ⟨K, M + 1, hK, fun x => ?_⟩
    rw [map_mul, norm_mul, MvPolynomial.eval_X, pow_succ, ← mul_assoc]
    have : ‖x i‖ ≤ 1 + ‖x‖ := by linarith [norm_le_pi_norm x i]
    exact mul_le_mul (h x) this (norm_nonneg _) (by positivity)
end GlobalTheory.FiniteCoverGrowth
