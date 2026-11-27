-- Prove2me | solution 1 for GlobalTheory.propDisc_of_flagDomainData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:04.373594+00:00
-- url     : https://prove2.me/submissions/d0e14a92-3f62-4474-8731-1d06238b3f2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPosOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PropDiscOfFlagDomainData
import Theorems.Thm_GlobalTheory_ClosedDiscontinuity_propDisc_and_la1GG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), PropDisc X :=
  fun _ _ _ _ => GlobalTheory.ClosedDiscontinuity.propDisc_and_la1GG.1
end GlobalTheory
