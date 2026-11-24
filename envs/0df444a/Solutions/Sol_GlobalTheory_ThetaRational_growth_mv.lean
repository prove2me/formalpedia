-- Prove2me | solution 1 for GlobalTheory.ThetaRational.growth_mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:32:52.487412+00:00
-- url     : https://prove2.me/submissions/7a9fb81b-35cb-452f-bf46-83f93afc9ed4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E : Type*} {n : ℕ}
namespace GlobalTheory.ThetaRational
theorem _root_.solution (q : MvPolynomial (Fin n) ℂ) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ x : Fin n → ℂ, ‖MvPolynomial.eval x q‖ ≤ C * (1 + ‖x‖) ^ m := by
  induction q using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, 0, norm_nonneg _, fun x => by simp⟩
  | add p q hp hq =>
    obtain ⟨C, m, hC, h⟩ := hp
    obtain ⟨C', m', hC', h'⟩ := hq
    refine ⟨C + C', m + m', by positivity, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by simp
    rw [map_add, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((h x).trans ?_) ((h' x).trans ?_))
    · gcongr; omega
    · gcongr; omega
  | mul_X p i hp =>
    obtain ⟨C, m, hC, h⟩ := hp
    refine ⟨C, m + 1, hC, fun x => ?_⟩
    rw [map_mul, norm_mul, MvPolynomial.eval_X, pow_succ, ← mul_assoc]
    have := norm_le_pi_norm x i
    have := h x
    gcongr
    linarith
end GlobalTheory.ThetaRational
