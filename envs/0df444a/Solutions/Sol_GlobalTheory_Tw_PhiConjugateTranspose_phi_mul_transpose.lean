-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.phi_mul_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:15.600105+00:00
-- url     : https://prove2.me/submissions/a3ba9e16-d4f4-4715-a290-bafd121f512d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_conj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.PhiConjugateTranspose
variable {n : ℕ} {R : Type} [CommRing R]
namespace GlobalTheory.Tw.PhiConjugateTranspose
theorem _root_.solution : Phi n R * (Phi n R)ᵀ = 1 := by
  have := phi_conj_apply (n := n) (R := R) 1
  ext i j
  have h := this i j
  rw [Matrix.mul_one] at h
  rw [h, one_apply, one_apply]
  by_cases hij : i = j
  · subst hij; simp [← mul_pow]
  · simp [hij]
end GlobalTheory.Tw.PhiConjugateTranspose
