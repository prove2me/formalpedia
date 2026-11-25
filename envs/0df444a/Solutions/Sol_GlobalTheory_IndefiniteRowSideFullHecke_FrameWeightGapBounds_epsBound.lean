-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds.epsBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:16.135357+00:00
-- url     : https://prove2.me/submissions/8515dd3a-f7ac-4ebb-ad74-cb64aaece928

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
theorem _root_.solution : EpsBound := by
  intro f k D T P h2 h6 hP hT
  have h2' : (2 : ℝ) ≤ ((f * k : ℕ) : ℝ) := by exact_mod_cast h2
  have h6' : (6 : ℝ) ≤ D := by exact_mod_cast h6
  have hkf : (k : ℝ) * f = ((f * k : ℕ) : ℝ) := by push_cast; ring
  set a : ℝ := ((f * k : ℕ) : ℝ) with ha
  have ha0 : 0 < a := by linarith
  have h3 : a ^ 3 ≤ P ^ 3 := pow_le_pow_left₀ ha0.le hP 3
  have hT' : a ^ 3 * ((D : ℝ) ^ 3 * a) ≤ T := by
    calc a ^ 3 * ((D : ℝ) ^ 3 * a) ≤ P ^ 3 * ((D : ℝ) ^ 3 * a) := by gcongr
      _ = P ^ 3 * (D : ℝ) ^ 3 * k * f := by rw [← hkf]; ring
      _ ≤ T := hT
  have hD : 4 * ((D : ℝ) * (D + 6)) ≤ (D : ℝ) ^ 3 * a := by
    have : (D : ℝ) ^ 3 * 2 ≤ (D : ℝ) ^ 3 * a := by gcongr
    nlinarith [mul_nonneg (sub_nonneg.2 h6') (sq_nonneg (D : ℝ)), sq_nonneg (D : ℝ)]
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT'
  rw [div_le_iff₀ hT0, inv_eq_one_div, div_div, div_mul_eq_mul_div, one_mul,
    le_div_iff₀ (by positivity)]
  have : a ^ 3 * (4 * ((D : ℝ) * (D + 6))) ≤ a ^ 3 * ((D : ℝ) ^ 3 * a) := by gcongr
  linarith
end GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
