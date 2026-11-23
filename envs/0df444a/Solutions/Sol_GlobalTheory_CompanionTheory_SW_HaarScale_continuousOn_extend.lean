-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarScale.continuousOn_extend
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:45.012805+00:00
-- url     : https://prove2.me/submissions/84d64af2-9d9e-4f32-b884-6fb993de9e99

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
theorem _root_.solution (A : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} → ℝ≥0)
    (hA : Continuous A) [∀ g : Matrix (Fin n) (Fin n) K, Decidable (IsUnit g.det)] :
    ContinuousOn (fun g : Matrix (Fin n) (Fin n) K => if h : IsUnit g.det then A ⟨g, h⟩ else 0)
      {g | IsUnit g.det} := by
  rw [continuousOn_iff_continuous_restrict]
  refine hA.congr fun g => ?_
  simp [Set.restrict, g.2]
end GlobalTheory.CompanionTheory.SW.HaarScale
