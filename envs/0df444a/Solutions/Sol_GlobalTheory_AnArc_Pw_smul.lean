-- Prove2me | solution 1 for GlobalTheory.AnArc.Pw_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:13:33.272583+00:00
-- url     : https://prove2.me/submissions/eddbd592-e94e-4ebf-a2a8-693cbac30e39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_degeneratingTori_basePeriodMap_smul
import Theorems.Thm_GlobalTheory_AnArc_N_smul

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
theorem _root_.solution (w : ℂ) (a : O) (v : A.La) : A.Pw w (a • v) = A.actV a (A.Pw w v) := by
  rw [Pw_apply, Pw_apply, degeneratingTori_basePeriodMap_smul, N_smul, map_add, map_smul]
end GlobalTheory.AnArc
