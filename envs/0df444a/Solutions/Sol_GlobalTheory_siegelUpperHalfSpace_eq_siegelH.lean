-- Prove2me | solution 1 for GlobalTheory.siegelUpperHalfSpace_eq_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:42.976197+00:00
-- url     : https://prove2.me/submissions/54b5760b-5a28-4366-b5bd-2e11a51441e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
namespace GlobalTheory
theorem _root_.solution (ι : Type*) [Fintype ι] :
    siegelUpperHalfSpace ι = ReciprocityTheory.PTheta.SiegelH ι := rfl
end GlobalTheory
