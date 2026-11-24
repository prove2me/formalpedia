-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarScale.conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:19.453966+00:00
-- url     : https://prove2.me/submissions/c0eadba0-0b92-422a-9f37-37b61d628fef

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_conjT_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_mem_hermR_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_conjT_conjT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarScale
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.HaarScale
theorem _root_.solution {σ : E →ₐ[F] E} (hs : ∀ x, σ (σ x) = x) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (S : HermR R σ n) :
    conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n := by
  rw [mem_hermR_iff, conjT_mul, conjT_mul, conjT_conjT R hs, (mem_hermR_iff R σ _).1 S.2, Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SW.HaarScale
