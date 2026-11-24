-- Prove2me | solution 1 for GlobalTheory.FibreHyp.bwd_fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:25.207477+00:00
-- url     : https://prove2.me/submissions/69d822d1-1f77-4e84-b689-2b6cf1c7523d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.FibreHyp
variable {A : Type} [CommRing A] {σ : Type} (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k]
namespace GlobalTheory.FibreHyp
theorem _root_.solution : (bwd2 f g k).comp (fwd f g k) = AlgHom.id k _ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply IsLocalization.algHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {f}) g))
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    have h1 := fibreHypersurfaceForwardQuotient_mk f g k (MvPolynomial.X i)
    have h2 := fibreHypersurfaceBackwardPolynomial_map f g k (MvPolynomial.X i)
    simp only [MvPolynomial.map_X, rhoK_apply, rhoA_apply] at h1 h2
    change bwd2 f g k (fwd f g k ((1 : k) ⊗ₜ[A] algebraMap _ (LA f g) (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.X i)))) =
      (1 : k) ⊗ₜ[A] algebraMap _ (LA f g) (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.X i))
    simp only [fwd, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul, fwd2, IsLocalization.Away.coe_liftAlgHom,
      IsLocalization.Away.lift_eq, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, bwd2, fibreHypersurfaceBackwardQuotient_mk, h2,
      Algebra.TensorProduct.includeRight_apply]
end GlobalTheory.FibreHyp
