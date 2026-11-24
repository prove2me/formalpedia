-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OM.SchDiff.temperate_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:22:13.333972+00:00
-- url     : https://prove2.me/submissions/5cd124f5-74b4-483e-bbda-0bb3e70da135

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OM GlobalTheory.CompanionTheory.OM.SchDiff
namespace GlobalTheory.CompanionTheory.OM.SchDiff
theorem _root_.solution : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have hd : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => cexp (I * t)) = fun t : ℝ => I ^ n * cexp (I * t) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have : HasDerivAt (fun t : ℝ => I ^ n * cexp (I * t)) (I ^ n * (cexp (I * t) * (I * 1))) t :=
        (((hasDerivAt_id (t : ℂ)).const_mul I).cexp.const_mul _).comp_ofReal
      rw [this.deriv]; ring
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n => ⟨0, 1, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp
end GlobalTheory.CompanionTheory.OM.SchDiff
