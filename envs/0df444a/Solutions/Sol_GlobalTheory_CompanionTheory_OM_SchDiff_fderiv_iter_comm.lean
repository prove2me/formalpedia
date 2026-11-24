-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OM.SchDiff.fderiv_iter_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:54:03.681445+00:00
-- url     : https://prove2.me/submissions/570cd931-4684-4acf-ad3c-bfb5252e09c5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_contDiff_iter

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
theorem _root_.solution {F : X → V} (hF : ContDiff ℝ ∞ F) (h : X) (n : ℕ) (a : X) :
    fderiv ℝ (iteratedFDeriv ℝ n F) a h = iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a := by
  induction n generalizing a with
  | zero =>
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((contDiff_iter hF 0).differentiable (by simp) a)]
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    ext m
    have hK := contDiff_iter hF n
    have hK' : ContDiff ℝ ∞ (fderiv ℝ (iteratedFDeriv ℝ n F)) := hK.fderiv_right (by norm_cast)
    have hd := hK'.differentiable (by simp) a
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((contDiff_iter hF (n + 1)).differentiable (by simp) a), iteratedFDeriv_succ_apply_left,
      ← funext ih]
    simp only [iteratedFDeriv_succ_apply_left]
    rw [fderiv_continuousMultilinear_apply_const_apply (hd.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
    have hs := (hK.contDiffAt (x := a)).isSymmSndFDerivAt (by simp; norm_cast)
    simp [hs.eq h (m 0)]
end GlobalTheory.CompanionTheory.OM.SchDiff
