-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OM.SchDiff.taylor_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:09:41.810384+00:00
-- url     : https://prove2.me/submissions/0a40245a-88b5-425c-b087-413b954c5b16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_contDiff_iter
import Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_fderiv_iter_comm

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
variable {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.CompanionTheory.OM.SchDiff
theorem _root_.solution {F : X → V} (hF : ContDiff ℝ ∞ F) (n : ℕ) (a h : X) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ segment ℝ a (a + h), ‖iteratedFDeriv ℝ (n + 2) F b‖ ≤ M) :
    ‖iteratedFDeriv ℝ n F (a + h) - iteratedFDeriv ℝ n F a
      - iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a‖ ≤ M * ‖h‖ * ‖h‖ := by
  have h1 : ∀ b ∈ segment ℝ a (a + h),
      ‖fderiv ℝ (iteratedFDeriv ℝ n F) b - fderiv ℝ (iteratedFDeriv ℝ n F) a‖ ≤ M * ‖h‖ := by
    intro b hb
    have h2 := (convex_segment a (a + h)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := iteratedFDeriv ℝ (n + 1) F) (C := M)
      (fun x _ => (contDiff_iter hF (n + 1)).differentiable (by simp) x)
      (fun x hx => by rw [norm_fderiv_iteratedFDeriv]; exact hM x hx)
      (left_mem_segment _ _ _) hb
    have h3 : ‖b - a‖ ≤ ‖h‖ := by
      simpa using norm_sub_le_of_mem_segment hb
    rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact h2.trans (by gcongr)
  have h4 := (convex_segment a (a + h)).norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ)
      (f := iteratedFDeriv ℝ n F)
      (fun x _ => (contDiff_iter hF n).differentiable (by simp) x) h1
      (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  rw [add_sub_cancel_left, fderiv_iter_comm hF] at h4
  exact h4
end GlobalTheory.CompanionTheory.OM.SchDiff
