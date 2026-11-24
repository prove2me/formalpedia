-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:26:40.79183+00:00
-- url     : https://prove2.me/submissions/5563eea8-6cf1-435d-ba11-abe7df355c5d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.KUnits
namespace GlobalTheory.CompanionTheory.SW.KUnits
theorem _root_.solution {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (h : IsOpenEmbedding (Units.val : Rˣ → R)) :
    ContinuousOn (Ring.inverse : R → R) {r | IsUnit r} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  refine (h.continuousAt_iff).1 ?_
  have : (Ring.inverse ∘ (Units.val : Rˣ → R)) = fun u : Rˣ => ((u⁻¹ : Rˣ) : R) := by
    funext v
    simp
  rw [this]
  exact (Units.continuous_val.comp continuous_inv).continuousAt
end GlobalTheory.CompanionTheory.SW.KUnits
