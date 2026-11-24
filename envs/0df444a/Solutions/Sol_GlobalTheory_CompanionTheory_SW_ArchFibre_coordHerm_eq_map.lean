-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArchFibre.coordHerm_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:26:45.016937+00:00
-- url     : https://prove2.me/submissions/6ea6f57f-b011-47c4-bef0-725593cde810

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_hermScal_qR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_continuous_hermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_coordHerm_qR

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
theorem _root_.solution (h : IsCMExt F E σ) [IsTopologicalRing R] [SecondCountableTopology R]
    (htr : Continuous (Algebra.trace R (R ⊗[F] E)))
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) [SigmaFinite lam] :
    coordHerm R σ b lam 1 = Measure.map (hermScal R σ) lam := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have hm : Measurable (hermScal R σ (F := F) (E := E)) := (continuous_hermScal R).measurable
  ext A hA
  rw [Measure.map_apply hm hA, ← coordHerm_qR R h htr b lam (hm hA)]
  congr 1
  ext S
  simp [hermScal_qR R h S]
end GlobalTheory.CompanionTheory.SW.ArchFibre
