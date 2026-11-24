-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RealCoord.coord_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:47.168805+00:00
-- url     : https://prove2.me/submissions/dd7ce248-614a-4a81-830a-2ba7a880fc60

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
theorem _root_.solution (y : Ainf F) (w : InfinitePlace F) :
    coord F y w = ringEquivRealOfIsReal (IsTotallyReal.isReal w) (y w) := rfl
end GlobalTheory.CompanionTheory.SW.RealCoord
