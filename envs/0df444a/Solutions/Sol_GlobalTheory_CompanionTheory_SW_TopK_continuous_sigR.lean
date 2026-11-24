-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TopK.continuous_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:08.538341+00:00
-- url     : https://prove2.me/submissions/1b9e4b52-99c7-4bcd-8538-90eada17b889

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TopK
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
omit [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.SW.TopK
theorem _root_.solution (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
end GlobalTheory.CompanionTheory.SW.TopK
