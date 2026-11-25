-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Axes.ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:11.529591+00:00
-- url     : https://prove2.me/submissions/2160079e-87d0-4964-9b73-b22d4321b666

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Theorems.Thm_GlobalTheory_ChartCmp_Axes_vec3
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_triple_points_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Axes
variable {R : Type} [CommRing R]
namespace GlobalTheory.ChartCmp.Axes
theorem _root_.solution {d n : ℕ} (f : PS R 3 d) (hf : ev (n := 2) ![pt R d 0, pt R d 1, 0] f = 1) (z : Pt R n d) (hz : GP z) :
    ev ![z, 0, 0] f = 1 := by
  have hV : ∀ j, GP (![z, (0 : Pt R n d)] j) := pair_points_zero_constant hz gp_zero₂
  have := congrArg (ev ![z, 0]) hf
  rw [gt_ev_ev' _ _ hV (triple_points_zero_constant (gp_pt 0) (gp_pt 1) gp_zero₂), vec3, evP_zero _ hV, evP_pt _ hV,
    evP_pt _ hV, ev_one] at this
  exact this
end GlobalTheory.ChartCmp.Axes
