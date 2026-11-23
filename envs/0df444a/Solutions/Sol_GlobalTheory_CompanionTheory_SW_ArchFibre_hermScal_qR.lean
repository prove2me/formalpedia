-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArchFibre.hermScal_qR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:18.472496+00:00
-- url     : https://prove2.me/submissions/30ac7ae3-1043-45cf-8c80-1342eeceb0c2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_conj_facts
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_fixed_eq_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_half_trace_tmul


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
variable (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.ArchFibre
theorem _root_.solution (h : IsCMExt F E σ) (S : HermR R σ 1) : hermScal R σ (qR R σ S) = S := by
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts h
  obtain ⟨r, hr⟩ := HaarCoord.fixed_eq_tmul R hinv h.2.2.1 hδ hσδ
    ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) (S.2 0 0)
  have hq : qR R σ S = r := by
    unfold qR
    rw [hr]
    exact HaarCoord.half_trace_tmul R h.2.2.1 r
  apply Subtype.ext
  funext a c
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : c = 0 := Subsingleton.elim _ _
  rw [hq, hr]
  rfl
end GlobalTheory.CompanionTheory.SW.ArchFibre
