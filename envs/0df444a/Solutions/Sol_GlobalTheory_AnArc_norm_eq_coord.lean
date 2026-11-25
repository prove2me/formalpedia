-- Prove2me | solution 1 for GlobalTheory.AnArc.norm_eq_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:31:31.565741+00:00
-- url     : https://prove2.me/submissions/16289d14-cb60-4a22-8638-78aacff6ba6c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero

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
theorem _root_.solution (l : A.X →+ ℂ) : ‖l‖ = ‖A.coord l‖ := rfl
end GlobalTheory.AnArc
