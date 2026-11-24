-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarScale.conjT_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:43.668359+00:00
-- url     : https://prove2.me/submissions/670840aa-3b1c-4d85-8e41-7a095bed1f22

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_sigR_sigR


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
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : conjT R σ (conjT R σ g) = g := by
  ext a b
  simp [conjT, GlobalTheory.CompanionTheory.SW.HermTop.sigR_sigR R hs]
end GlobalTheory.CompanionTheory.SW.HaarScale
