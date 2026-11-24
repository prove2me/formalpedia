-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.theta_blockTriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:28.141037+00:00
-- url     : https://prove2.me/submissions/9d1437c8-7034-418f-be1c-3ffcb866c67f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_conj_apply
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_theta_eq

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
variable [StarRing R]
namespace GlobalTheory.Tw.PhiConjugateTranspose
theorem _root_.solution {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) (ht : g.BlockTriangular id) :
    (theta g).BlockTriangular id := by
  have : Invertible g := hg.invertible
  have hi : (g⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  intro i j hji
  rw [theta_eq, phi_conj_apply, conjTranspose_apply, hi]
  · simp
  · simpa [Fin.rev_lt_rev] using hji
end GlobalTheory.Tw.PhiConjugateTranspose
