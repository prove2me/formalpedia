-- Prove2me | solution 1 for GlobalTheory.T.completion_is_local_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:00:47.404054+00:00
-- url     : https://prove2.me/submissions/3e6d6179-da21-4d8d-be6e-e506acff04d1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFv_isLocR_Fv


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), IsLocR (Fv F v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv | exact GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv | (intros; apply GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv <;> assumption)
end _root_.GlobalTheory.T
