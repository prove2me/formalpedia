-- Prove2me | solution 1 for GlobalTheory.AffinePoints.surjective_comap_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:41.122719+00:00
-- url     : https://prove2.me/submissions/36c98c76-3197-4d67-b36b-ffc6887d2f69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Theorems.Thm_GlobalTheory_AffinePoints_exists_comap_eq_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set Polynomial
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
namespace GlobalTheory.AffinePoints
theorem _root_.solution {K A B : Type*} [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral)
    (hinj : Function.Injective φ) :
    Function.Surjective (comap φ : (B →ₐ[K] K) → (A →ₐ[K] K)) := fun p =>
  exists_comap_eq_of_isIntegral φ hφ p fun a ha => by
    rw [(injective_iff_map_eq_zero φ).1 hinj a ha, map_zero]
end GlobalTheory.AffinePoints
