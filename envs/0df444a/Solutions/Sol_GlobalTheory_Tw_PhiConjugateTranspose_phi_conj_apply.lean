-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.phi_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:03.168055+00:00
-- url     : https://prove2.me/submissions/7ff8d3d3-7a56-4d5d-befb-e420d4a8512d

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Phi n R * A * (Phi n R)ᵀ) i j = (-1 : R) ^ (i : ℕ) * A i.rev j.rev * (-1 : R) ^ (j : ℕ) := by
  simp [mul_apply, phi_apply, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]
end GlobalTheory.Tw.PhiConjugateTranspose
