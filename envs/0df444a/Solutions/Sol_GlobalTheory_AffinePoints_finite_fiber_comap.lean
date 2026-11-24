-- Prove2me | solution 1 for GlobalTheory.AffinePoints.finite_fiber_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:36.086069+00:00
-- url     : https://prove2.me/submissions/0082690f-9cb9-48a5-9223-7985b2ef1764

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne

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
theorem _root_.solution {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [Field K] [Algebra R K] (φ : A →ₐ[R] B) (hφ : φ.Finite) (p : A →ₐ[R] K) :
    ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}).Finite := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra A K := p.toRingHom.toAlgebra
  haveI : Module.Finite A B := hφ
  let F : ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}) → (B →ₐ[A] K) := fun q =>
    { q.1.toRingHom with commutes' := fun a => DFunLike.congr_fun q.2 a }
  refine Set.finite_coe_iff.1 (Finite.of_injective F fun q q' h => ?_)
  ext b
  exact DFunLike.congr_fun h b
end GlobalTheory.AffinePoints
