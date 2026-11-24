-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.trace_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:25.521344+00:00
-- url     : https://prove2.me/submissions/44cc5d4d-3617-42c9-9518-7d64754f086f

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_trace_tmul
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
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
namespace GlobalTheory.CompanionTheory.SelfDualInf
theorem _root_.solution [Algebra.IsSeparable F E] (z : R ⊗[F] E)
    (h : ∀ u, Algebra.trace R (R ⊗[F] E) (z * u) = 0) : z = 0 := by
  classical
  let b := Module.finBasis F E
  let B := Algebra.traceForm F E
  have hB : B.Nondegenerate := traceForm_nondegenerate F E
  let b' := B.dualBasis hB b
  let c := Algebra.TensorProduct.basis R b
  have hz : z = ∑ i, c.repr z i ⊗ₜ[F] b i := by
    conv_lhs => rw [← c.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [c, TensorProduct.smul_tmul']
  have hc : ∀ j, c.repr z j = 0 := by
    intro j
    have h1 := h ((1 : R) ⊗ₜ[F] b' j)
    rw [hz, Finset.sum_mul, map_sum] at h1
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, trace_tmul] at h1
    rw [Finset.sum_eq_single j] at h1
    · have h2 : Algebra.trace F E (b j * b' j) = 1 := by
        have := LinearMap.BilinForm.apply_dualBasis_right hB (Algebra.traceForm_isSymm F) b j j
        simpa [B, b', Algebra.traceForm_apply] using this
      rw [h2, map_one, mul_one] at h1
      exact h1
    · intro i _ hij
      have h2 : Algebra.trace F E (b i * b' j) = 0 := by
        have := LinearMap.BilinForm.apply_dualBasis_right hB (Algebra.traceForm_isSymm F) b i j
        simpa [B, b', Algebra.traceForm_apply, hij] using this
      rw [h2, map_zero, mul_zero]
    · simp
  rw [← c.sum_repr z]
  simp [hc]
end GlobalTheory.CompanionTheory.SelfDualInf
