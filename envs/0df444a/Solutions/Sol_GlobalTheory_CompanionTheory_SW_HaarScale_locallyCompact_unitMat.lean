-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarScale.locallyCompact_unitMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:01.429857+00:00
-- url     : https://prove2.me/submissions/aeca0a59-84de-4576-a53c-5d94bb37bd85

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale

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
variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.HaarScale
theorem _root_.solution [LocallyCompactSpace K] (hu : IsOpenEmbedding (Units.val : Kˣ → K)) :
    LocallyCompactSpace {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → K))
  have hset : {g : Matrix (Fin n) (Fin n) K | IsUnit g.det} =
      (fun g : Matrix (Fin n) (Fin n) K => g.det) ⁻¹' Set.range (Units.val : Kˣ → K) := by
    ext g; simp [IsUnit]
  have hopen : IsOpen {g : Matrix (Fin n) (Fin n) K | IsUnit g.det} := by
    rw [hset]
    exact hu.isOpen_range.preimage (Continuous.matrix_det continuous_id)
  exact hopen.isOpenEmbedding_subtypeVal.locallyCompactSpace
end GlobalTheory.CompanionTheory.SW.HaarScale
