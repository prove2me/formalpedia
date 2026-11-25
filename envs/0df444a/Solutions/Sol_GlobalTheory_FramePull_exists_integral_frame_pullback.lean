-- Prove2me | solution 1 for GlobalTheory.FramePull.exists_integral_frame_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:07:51.307601+00:00
-- url     : https://prove2.me/submissions/f9a318a0-6bcf-4ce6-9914-937df081076c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_GlobalTheory_FramePull_ExpIntegral_add
import Theorems.Thm_GlobalTheory_FramePull_ExpIntegral_neg
import Theorems.Thm_GlobalTheory_FramePull_expIntegral_ad
import Theorems.Thm_GlobalTheory_FramePull_expIntegral_nsmul
import Theorems.Thm_GlobalTheory_FramePull_ev_actK_hL
import Theorems.Thm_GlobalTheory_FramePull_hL_eq

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
namespace GlobalTheory.FramePull
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
      [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h →
      ∀ (w0 a : O) (N : ℕ), a * star a = (N : O) → ∃ w : PS R 1 d, constantCoeff w = 1 ∧
        FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N hN
  have h1 := expIntegral_ad hh a 1 (w0 * a)
  have h2 := (expIntegral_nsmul hh 1 w0 N).neg
  have e : star a * (w0 * a) = (N : O) * w0 := by rw [← hN]; ring
  rw [e, _root_.mul_one] at h1
  have h3 := (h1.add h2).2
  rw [ev_actK_hL, hL_eq]
  convert h3 using 5
  ring
end GlobalTheory.FramePull
