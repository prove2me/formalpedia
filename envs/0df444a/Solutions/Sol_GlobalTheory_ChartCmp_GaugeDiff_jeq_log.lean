-- Prove2me | solution 1 for GlobalTheory.ChartCmp.GaugeDiff.jeq_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:02.694505+00:00
-- url     : https://prove2.me/submissions/f25cfb64-ddd5-4192-aec1-5f33fbda0130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
import Theorems.Thm_GlobalTheory_ChartCmp_jeq_expS_iff_and_exists_log
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add


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
variable [Algebra ℚ k]
namespace GlobalTheory.ChartCmp.GaugeDiff
theorem _root_.solution {n m : ℕ} {A B C D : PS k n d} (hA : constantCoeff A = 0) (hB : constantCoeff B = 0)
    (hC : constantCoeff C = 0) (hD : constantCoeff D = 0)
    (h : JEq m (FB.expS k A * FB.expS k B) (FB.expS k C * FB.expS k D)) : JEq m (A + B) (C + D) := by
  rw [← gt_expS_add _ _ hA hB, ← gt_expS_add _ _ hC hD] at h
  exact ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k n d m).1 _ _ (by simp [hA, hB]) (by simp [hC, hD])).2 h
end GlobalTheory.ChartCmp.GaugeDiff
