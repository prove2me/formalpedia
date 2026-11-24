-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermTop.continuous_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:12.990799+00:00
-- url     : https://prove2.me/submissions/44fcf559-d625-4721-8f2c-067ff5679229

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_isModTop
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_isTopRing

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.SW.HermTop
theorem _root_.solution [Module.Finite F E] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
end GlobalTheory.CompanionTheory.SW.HermTop
