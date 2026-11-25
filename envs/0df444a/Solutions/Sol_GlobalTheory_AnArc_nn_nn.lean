-- Prove2me | solution 1 for GlobalTheory.AnArc.nn_nn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:34:26.836977+00:00
-- url     : https://prove2.me/submissions/6eff0208-47d8-466a-9e98-25f3de2795e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_nn_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (v : A.La) : A.nn (A.nn v) = 0 := by ext <;> simp [nn_apply]
end GlobalTheory.AnArc
