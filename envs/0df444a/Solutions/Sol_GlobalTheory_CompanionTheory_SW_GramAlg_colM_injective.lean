-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramAlg.colM_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:19:03.271746+00:00
-- url     : https://prove2.me/submissions/97f03118-fbda-4c45-b3fd-0172e1d6e3bf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {A : Type} [CommRing A] {M n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.GramAlg
theorem _root_.solution : Function.Injective (colM : (Fin n → Fin M → A) → _) := by
  intro X Y h
  funext a i
  exact congrFun (congrFun h i) a
end GlobalTheory.CompanionTheory.SW.GramAlg
