-- Prove2me | solution 1 for GlobalTheory.GaugeInt.ev_defR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:24.945738+00:00
-- url     : https://prove2.me/submissions/86f143f8-581d-4661-9e8f-cebd21f8b8d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
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
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv
open GlobalTheory GlobalTheory.GaugeInt
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
variable {φ}
namespace GlobalTheory.GaugeInt
theorem _root_.solution (F : Pt k 2 d) (hF : GP F) (g : PS k 2 d)
    {n : ℕ} (a b c : Pt k n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, b, c] (defR F g) = ev ![a, b] g + ev ![a, c] g - ev ![a, addOf F b c] g := by
  have hV := triple_points_zero_constant ha hb hc
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  rw [defR, gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (gp_addOf F hF _ _ (hp _) (hp _))), eval_pair_points, eval_pair_points, eval_pair_points,
    evP_addOf _ hV F _ _ (hp _) (hp _)]
  simp only [evP_pt _ hV]
  rfl
end GlobalTheory.GaugeInt
