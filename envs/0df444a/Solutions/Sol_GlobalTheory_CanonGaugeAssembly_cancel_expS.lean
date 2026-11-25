-- Prove2me | solution 1 for GlobalTheory.CanonGaugeAssembly.cancel_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:06:37.791364+00:00
-- url     : https://prove2.me/submissions/ee37c02f-1e5b-4cf1-ba13-2d8d7c91de42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeOfSteps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_expS_zero


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
open GlobalTheory GlobalTheory.CanonGaugeAssembly
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.CanonGaugeAssembly
theorem _root_.solution [Algebra ℚ k] {n : ℕ} {p c : PS k n d} (hc : constantCoeff c = 0)
    (e : FB.expS k c = p * FB.expS k c) : p = 1 := by
  have u : FB.expS k c * FB.expS k (-c) = 1 := by
    rw [← gt_expS_add _ _ hc (by rw [map_neg, hc, neg_zero]), add_neg_cancel, nt_expS_zero]
  calc p = p * FB.expS k c * FB.expS k (-c) := by rw [mul_assoc, u, mul_one]
    _ = 1 := by rw [← e, u]
end GlobalTheory.CanonGaugeAssembly
