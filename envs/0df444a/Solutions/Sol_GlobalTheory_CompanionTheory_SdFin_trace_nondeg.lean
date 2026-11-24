-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SdFin.trace_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:21:59.004784+00:00
-- url     : https://prove2.me/submissions/65c966fb-78fb-4428-ab4f-442f70f433bc

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_trace_tmul
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SdFin
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
namespace GlobalTheory.CompanionTheory.SdFin
theorem _root_.solution [FiniteDimensional F E] [Algebra.IsSeparable F E] (z : R ⊗[F] E)
    (h : ∀ w, Algebra.trace R (R ⊗[F] E) (z * w) = 0) : z = 0 := by
  classical
  let b := Module.finBasis F E
  let b' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b
  have key : ∀ (k) (z : R ⊗[F] E), (Algebra.TensorProduct.basis R b').repr z k =
      Algebra.trace R (R ⊗[F] E) (z * (1 : R) ⊗ₜ[F] b k) := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_mul]
    | tmul a e =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, trace_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp [b', LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  refine (Algebra.TensorProduct.basis R b').ext_elem fun k => ?_
  rw [key, h]; simp
end GlobalTheory.CompanionTheory.SdFin
