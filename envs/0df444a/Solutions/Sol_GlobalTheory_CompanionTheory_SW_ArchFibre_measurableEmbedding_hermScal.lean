-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArchFibre.measurableEmbedding_hermScal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:35.090922+00:00
-- url     : https://prove2.me/submissions/3d6587a5-c6bd-4185-9807-bace5e2d1ca9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_qR_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_hermScal_qR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_continuous_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_continuous_qR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ArchFibre
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
variable [MeasurableSpace R] [BorelSpace R]
namespace GlobalTheory.CompanionTheory.SW.ArchFibre
theorem _root_.solution (h : IsCMExt F E σ) [IsTopologicalRing R]
    (htr : Continuous (Algebra.trace R (R ⊗[F] E))) :
    MeasurableEmbedding (hermScal R σ (F := F) (E := E)) := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  let e : R ≃ᵐ HermR R σ 1 :=
    { toFun := hermScal R σ
      invFun := qR R σ
      left_inv := qR_hermScal R h
      right_inv := hermScal_qR R h
      measurable_toFun := (continuous_hermScal R).measurable
      measurable_invFun := (continuous_qR R htr).measurable }
  exact e.measurableEmbedding
end GlobalTheory.CompanionTheory.SW.ArchFibre
