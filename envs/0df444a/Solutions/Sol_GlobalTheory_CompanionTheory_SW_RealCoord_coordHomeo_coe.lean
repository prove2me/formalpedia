-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:46.258039+00:00
-- url     : https://prove2.me/submissions/dc5b158f-516f-4bf8-9f69-3909cb80cfee

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
theorem _root_.solution : ⇑(coordHomeo F) = ⇑(coord F) := rfl
end GlobalTheory.CompanionTheory.SW.RealCoord
