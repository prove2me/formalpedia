-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RealCoord.toMixed_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:48.034306+00:00
-- url     : https://prove2.me/submissions/c7c410b8-455b-40db-888f-3c43a32ec0eb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RealCoord
open InfinitePlace InfinitePlace.Completion
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.CompanionTheory.SW.RealCoord
theorem _root_.solution : Function.Injective (toMixed F) := by
  intro y z h
  funext w
  exact congrFun (congrArg Prod.fst h) ⟨w, IsTotallyReal.isReal w⟩
end GlobalTheory.CompanionTheory.SW.RealCoord
