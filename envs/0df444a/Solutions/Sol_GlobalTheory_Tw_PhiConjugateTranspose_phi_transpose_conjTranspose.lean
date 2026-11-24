-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.phi_transpose_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:26.763073+00:00
-- url     : https://prove2.me/submissions/9b844275-973a-419f-bc39-e877dd20bd1d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties

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
theorem _root_.solution : ((Phi n R)ᵀ)ᴴ = Phi n R := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, Phi, of_apply]
  split_ifs <;> simp
end GlobalTheory.Tw.PhiConjugateTranspose
