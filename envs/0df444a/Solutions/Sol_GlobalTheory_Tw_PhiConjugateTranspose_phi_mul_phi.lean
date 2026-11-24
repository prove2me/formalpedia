-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.phi_mul_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:25.983801+00:00
-- url     : https://prove2.me/submissions/2b7f6706-6cc0-4e66-8298-8ee8f010f526

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Theorems.Thm_GlobalTheory_Tw_PhiConjugateTranspose_phi_apply

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
theorem _root_.solution : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i k
  simp only [mul_apply, phi_apply, Matrix.smul_apply, one_apply, smul_eq_mul, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h : k = i
  · subst h
    simp only [if_true, mul_one]
    rw [← pow_add, Fin.val_rev]
    have hk := k.isLt
    rw [show (k : ℕ) + (n - ((k : ℕ) + 1)) = n - 1 by omega]
  · simp [h, Ne.symm h]
end GlobalTheory.Tw.PhiConjugateTranspose
