-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceFormGram.trace_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:35:07.361802+00:00
-- url     : https://prove2.me/submissions/c0cf76b9-0789-44f4-9b67-051755364fa9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceFormGram
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.TraceFormGram
theorem _root_.solution [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    ext y
    simp [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul]
  have h2 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    simp [TensorProduct.smul_tmul']
  rw [h2, map_smul, h1, smul_eq_mul]
end GlobalTheory.CompanionTheory.SW.TraceFormGram
