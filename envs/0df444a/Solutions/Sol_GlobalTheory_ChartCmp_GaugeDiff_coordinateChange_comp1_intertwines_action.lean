-- Prove2me | solution 1 for GlobalTheory.ChartCmp.GaugeDiff.coordinateChange_comp1_intertwines_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:11.289078+00:00
-- url     : https://prove2.me/submissions/eba23dd9-31d7-4906-beb2-a70ad671e9c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp_inv


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
theorem _root_.solution {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (A A' : Pt k 1 d) (hAa : GP A)
    (hA : A' = comp1 φi (comp1 A φ)) (x : Pt k n d) (hx : GP x) :
    comp1 φ (comp1 A' x) = comp1 A (comp1 φ x) := by
  have hφ : GP φ := hinv.1
  rw [hA, gt_comp1_comp1 φi _ (gp_comp1 _ φ hAa hφ) x hx, gt_comp1_comp1 A φ hφ x hx,
    gt_comp_inv hinv _ (gp_comp1 _ _ hAa (gp_comp1 _ _ hφ hx))]
end GlobalTheory.ChartCmp.GaugeDiff
