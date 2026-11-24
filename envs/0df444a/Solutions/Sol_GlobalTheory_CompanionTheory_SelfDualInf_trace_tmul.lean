-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.trace_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:24.802055+00:00
-- url     : https://prove2.me/submissions/5bd66034-7384-4a07-b396-a2d58aa65213

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
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
theorem _root_.solution (r : R) (x : E) : Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) =
    r * algebraMap F R (Algebra.trace F E x) := by
  have h : Algebra.lmul R (R ⊗[F] E) (r ⊗ₜ[F] x) =
      r • (Algebra.lmul F E x).baseChange R := by
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    ext y
    simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', mul_comm]
  rw [Algebra.trace_apply, h, map_smul, LinearMap.trace_baseChange, smul_eq_mul, Algebra.trace_apply]
end GlobalTheory.CompanionTheory.SelfDualInf
