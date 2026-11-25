-- Prove2me | solution 1 for GlobalTheory.FramePull.ExpIntegral.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:39.088542+00:00
-- url     : https://prove2.me/submissions/b7381c00-1ec8-4dcc-806c-59de61f2deab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_zero


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
variable (R : Type) [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {R}
namespace GlobalTheory.FramePull
namespace ExpIntegral
theorem _root_.solution {f : PS k 1 d} (hf : ExpIntegral R f) : ExpIntegral R (-f) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  have n0 : constantCoeff (-f) = 0 := by simp [f0]
  refine ⟨n0, invOfUnit v 1, by simp, ?_⟩
  have h1 : FB.toK k v * FB.toK k (invOfUnit v 1) = 1 := by
    rw [FB.toK, FB.toK, ← map_mul, mul_invOfUnit v 1 (by simpa using v1), map_one]
  have h2 : FB.expS k (-f) * FB.expS k f = 1 := by
    unfold FB.expS
    rw [← WickVanishing.exp_add n0 f0, neg_add_cancel, WickVanishing.exp_zero]
  rw [hv] at h1
  calc FB.toK k (invOfUnit v 1) = (FB.expS k (-f) * FB.expS k f) * FB.toK k (invOfUnit v 1) := by
        rw [h2, _root_.one_mul]
    _ = FB.expS k (-f) := by rw [_root_.mul_assoc, h1, _root_.mul_one]
end ExpIntegral
end GlobalTheory.FramePull
