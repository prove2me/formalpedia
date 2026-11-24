-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarScale.map_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:45.289797+00:00
-- url     : https://prove2.me/submissions/3fac994b-ffb8-4e0d-9b46-608f053f39a1

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
variable {V P : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace P] [LocallyCompactSpace P]
namespace GlobalTheory.CompanionTheory.SW.HaarScale
theorem _root_.solution (μ : Measure V) [μ.IsAddHaarMeasure] (T Ti : V → V) (hT : Continuous T)
    (hTi : Continuous Ti) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hl : ∀ x, Ti (T x) = x) (hr : ∀ x, T (Ti x) = x) :
    ∃ c : ℝ≥0, μ.map T = c • μ := by
  haveI : (μ.map T).IsAddHaarMeasure :=
    (addEquivOf T Ti hadd hl hr).isAddHaarMeasure_map μ hT hTi
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
end GlobalTheory.CompanionTheory.SW.HaarScale
