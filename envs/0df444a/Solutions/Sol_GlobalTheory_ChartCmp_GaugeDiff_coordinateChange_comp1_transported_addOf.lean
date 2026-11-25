-- Prove2me | solution 1 for GlobalTheory.ChartCmp.GaugeDiff.coordinateChange_comp1_transported_addOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:54:34.191157+00:00
-- url     : https://prove2.me/submissions/c91d09bd-0b18-4847-9545-84866bd9bc78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


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
theorem _root_.solution {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (F F' : Fin d → PS k 2 d) (hBF : GP F)
    (hF : ∀ i, F' i = transF F φ φi i) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    comp1 φ (addOf F' a b) = addOf F (comp1 φ a) (comp1 φ b) := by
  have hφ : GP φ := hinv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hcφ : ∀ {n : ℕ} (a : Pt k n d), GP a → GP (comp1 φ a) := fun a ha => gp_comp1 φ a hφ ha
  have hAd : GP (addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) :=
    gp_addOf _ hBF _ _ (hcφ _ (hp 0)) (hcφ _ (hp 1))
  have e : addOf F' a b = comp1 φi (addOf F (comp1 φ a) (comp1 φ b)) := by
    funext i
    change ev ![a, b] (F' i) = ev ![addOf F (comp1 φ a) (comp1 φ b)] (φi i)
    rw [hF i]
    change ev ![a, b] (ev ![addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))]
      (φi i)) = _
    rw [gt_ev_ev' ![a, b] _ (pair_points_zero_constant ha hb) (single_point_zero_constant hAd)]
    congr 1
    funext j
    fin_cases j
    change evP ![a, b] (addOf F (comp1 φ (pt k d 0)) (comp1 φ (pt k d 1))) = _
    rw [evP_addOf _ (pair_points_zero_constant ha hb) _ _ _ (hcφ _ (hp 0)) (hcφ _ (hp 1)),
      evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (hp 0), evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (hp 1),
      evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
    rfl
  rw [e, gt_comp_inv hinv _ (gp_addOf _ hBF _ _ (hcφ _ ha) (hcφ _ hb))]
end GlobalTheory.ChartCmp.GaugeDiff
