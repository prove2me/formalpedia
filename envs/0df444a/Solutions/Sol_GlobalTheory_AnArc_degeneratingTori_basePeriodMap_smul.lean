-- Prove2me | solution 1 for GlobalTheory.AnArc.degeneratingTori_basePeriodMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:41:52.489976+00:00
-- url     : https://prove2.me/submissions/7202a536-c0e0-423f-9fc8-fb1f8022a29e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_H_F

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
theorem _root_.solution (a : O) (v : A.La) : A.P0 (a • v) = A.actV a (A.P0 v) := by
  refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
  · simp [A.T_adj, A.ct_smul, H_F]
  · simp [A.ct_smul]
end GlobalTheory.AnArc
