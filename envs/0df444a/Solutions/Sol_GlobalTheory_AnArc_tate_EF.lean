-- Prove2me | solution 1 for GlobalTheory.AnArc.tate_EF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:25:09.817808+00:00
-- url     : https://prove2.me/submissions/a34ee32e-cc88-434c-a447-0f74787c0353

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_EF_n_y

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
theorem _root_.solution (τ₀ : ℂ) : (tate τ₀).EF (La.mk (A := tate τ₀) 0 (AddMonoidHom.id ℤ) 0)
    (La.mk (A := tate τ₀) (1 : ℤ) 0 0) = -1 := (tate τ₀).EF_n_y _ _
end GlobalTheory.AnArc
