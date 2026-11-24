-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.stDelta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:25:21.528751+00:00
-- url     : https://prove2.me/submissions/f561e746-cdfb-4b33-92f2-8a83d0a4af5c

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DeltaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_exists_isDelta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl
namespace GlobalTheory.CompanionTheory.RgFl
theorem _root_.solution : StDelta := fun L _ _ _ _ s hs => exists_isDelta L s hs
end GlobalTheory.CompanionTheory.RgFl
