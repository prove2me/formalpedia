-- Prove2me | solution 1 for GlobalTheory.ChartCmp.GaugeDiff.ev_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:36.632968+00:00
-- url     : https://prove2.me/submissions/56d4769a-fe50-4524-bb0a-89e9c2433a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
import Theorems.Thm_GlobalTheory_ChartCmp_GaugeDiff_germEv_germEv_two_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open MvPowerSeries
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.GaugeDiff
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartCmp.GaugeDiff
theorem _root_.solution {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (h : PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) =
      ev ![comp1 φ a, comp1 φ b] h := by
  rw [germEv_germEv_two_points _ (pair_points_zero_constant ha hb) _ _ (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1)),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 0),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 1), evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
  rfl
end GlobalTheory.ChartCmp.GaugeDiff
