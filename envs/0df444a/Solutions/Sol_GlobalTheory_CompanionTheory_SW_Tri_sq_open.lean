-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Tri.sq_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:35:10.013286+00:00
-- url     : https://prove2.me/submissions/253ab3a0-1b20-416f-8093-70761bb74fa3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotentStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHermitianDiagonalizationUnitsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroup

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Tri
variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}
variable [TopologicalSpace R] [TopologicalSpace K] [IsTopologicalRing R] [IsTopologicalRing K]
namespace GlobalTheory.CompanionTheory.SW.Tri
theorem _root_.solution (U : Subgroup Rˣ) (hU : IsOpenEmbedding (fun u : U => ((u : Rˣ) ^ 2 : Rˣ)))
    (d : Fin n → Rˣ) :
    IsOpenEmbedding (fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) =>
      ((fun i => (p.1 i : Rˣ) ^ 2 * d i : Fin n → Rˣ), p.2)) :=
  (IsOpenEmbedding.piMap fun i => (Homeomorph.mulRight (d i)).isOpenEmbedding.comp hU).prodMap
    IsOpenEmbedding.id
end GlobalTheory.CompanionTheory.SW.Tri
