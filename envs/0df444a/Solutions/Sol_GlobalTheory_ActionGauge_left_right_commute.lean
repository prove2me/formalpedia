-- Prove2me | solution 1 for GlobalTheory.ActionGauge.left_right_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:06.295946+00:00
-- url     : https://prove2.me/submissions/cd1ee993-fa8e-4929-91dc-d6b0dd919922

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsActionGauge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.ActionGauge
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}
variable {O : Type} [CommRing O] {G : FGLaw k d} (A : OAct O G)
namespace GlobalTheory.ActionGauge
theorem _root_.solution (a b : O) : Commute (leftHom A a) (rightHom A b) := by
  refine LinearMap.ext fun g => Subtype.ext ?_
  change (leftMap A a (rightMap A b g) : PS k 2 d) = rightMap A b (leftMap A a g)
  rw [leftMap_val, rightMap_val, rightMap_val, leftMap_val,
    ev_right _ (A.const b) _ _ (gp_comp1 _ _ (A.const a) (gp_pt 0)) (gp_pt 1),
    ev_left _ (A.const a) _ _ (gp_pt 0) (gp_comp1 _ _ (A.const b) (gp_pt 1))]
end GlobalTheory.ActionGauge
