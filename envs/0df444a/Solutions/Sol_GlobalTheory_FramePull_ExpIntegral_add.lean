-- Prove2me | solution 1 for GlobalTheory.FramePull.ExpIntegral.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:33.150332+00:00
-- url     : https://prove2.me/submissions/0ef43990-1b56-4ce5-a4b3-8d3ea44aa420

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add


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
theorem _root_.solution {f g : PS k 1 d} (hf : ExpIntegral R f) (hg : ExpIntegral R g) :
    ExpIntegral R (f + g) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  obtain ⟨g0, w, w1, hw⟩ := hg
  refine ⟨by simp [f0, g0], v * w, by simp [v1, w1], ?_⟩
  rw [FB.toK, map_mul]
  unfold FB.expS
  rw [WickVanishing.exp_add f0 g0]
  exact congrArg₂ (· * ·) hv hw
end ExpIntegral
end GlobalTheory.FramePull
