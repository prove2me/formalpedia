-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OM.SchDiff.iter_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:54:05.195243+00:00
-- url     : https://prove2.me/submissions/d44addcb-cbd5-4157-b2e2-c98762a84b2a

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
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.CompanionTheory.OM.SchDiff
theorem _root_.solution {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) (p : P) (x : E) :
    iteratedFDeriv ℝ n (fun y => F (p, y)) x =
      (iteratedFDeriv ℝ n F (p, x)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  have h1 : (fun y => F (p, y)) = (fun q => F ((p, 0) + q)) ∘ ContinuousLinearMap.inr ℝ P E := by
    funext y; simp
  have h2 : ContDiff ℝ ∞ (fun q => F ((p, 0) + q)) := hF.comp (contDiff_const.add contDiff_id)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ h2 _ (by norm_cast; simp),
    iteratedFDeriv_comp_add_left]
  simp
end GlobalTheory.CompanionTheory.OM.SchDiff
