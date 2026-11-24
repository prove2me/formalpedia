-- Prove2me | solution 1 for GlobalTheory.FramePull.ev_actK_hL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:07:14.625147+00:00
-- url     : https://prove2.me/submissions/976833b2-78ed-4b4d-a27b-47498b6db0d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_point
import Theorems.Thm_GlobalTheory_FramePull_cz1
import Theorems.Thm_GlobalTheory_FramePull_germEv_germEv_two_points
import Theorems.Thm_GlobalTheory_FramePull_ev_point_fun
import Theorems.Thm_GlobalTheory_FramePull_ev_comp1
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_comp1
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_actK
import Theorems.Thm_GlobalTheory_FramePull_actK_mul

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FramePull
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O)
variable {B} {h : PS k 2 d}
omit [Algebra ℚ k]
namespace GlobalTheory.FramePull
theorem _root_.solution (w0 a : O) :
    ev (n := 1) ![B.actK k a] (B.hL k h w0) = ev ![B.actK k a, B.actK k (w0 * a)] h := by
  have hb := cz1 (constantCoeff_actK (k := k) B a)
  rw [FB.hL, germEv_germEv_two_points (constantCoeff_point 0) (constantCoeff_comp1 (constantCoeff_actK B w0)
    (constantCoeff_point 0)) hb, ev_comp1 _ (constantCoeff_point 0) hb, ev_point_fun hb, actK_mul]
  rfl
end GlobalTheory.FramePull
