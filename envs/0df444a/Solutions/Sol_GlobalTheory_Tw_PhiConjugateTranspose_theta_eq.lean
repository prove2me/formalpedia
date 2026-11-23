-- Prove2me | solution 1 for GlobalTheory.Tw.PhiConjugateTranspose.theta_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:16.659934+00:00
-- url     : https://prove2.me/submissions/067b0ed8-fd0d-426c-a5e9-4523974d979e

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
theorem _root_.solution (g : Matrix (Fin n) (Fin n) R) : theta g = Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ := rfl
end GlobalTheory.Tw.PhiConjugateTranspose
