-- Prove2me | solution 1 for GlobalTheory.AnArc.La.eq_add_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:44.536395+00:00
-- url     : https://prove2.me/submissions/e56c2fd9-9dd8-4aad-a578-d5c55fa46f7b

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
open GlobalTheory.AnArc.La
variable {A}
namespace GlobalTheory.AnArc.La
theorem _root_.solution (v : A.La) : v = mk v.y 0 0 + mk 0 v.n 0 + mk 0 0 v.l := by ext <;> simp
end GlobalTheory.AnArc.La
