-- Prove2me | solution 1 for OAI.Problem313.biased_two_point_fourth_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:01:46.902985+00:00
-- url     : https://prove2.me/submissions/4a4d5912-debf-4f9c-967b-ba32ec6ef095

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/TwoPoint.lean:L14-L35
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.biased_two_point_fourth_moment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption

-- ---- from OAI.Combinatorics.SharpThreshold.TwoPoint ----
namespace OAI

noncomputable section

namespace Problem313

/-- A pointwise fourth-power estimate with the linear term retained for averaging. -/
lemma fourth_power_centered_bound (a z : ℝ) :
    (a + z) ^ 4 ≤ a ^ 4 + 4 * a ^ 3 * z + 8 * a ^ 2 * z ^ 2 + 3 * z ^ 4 := by
  nlinarith only [sq_nonneg (z * (a - z))]

/-- The scalar two-point estimate used to tensorize biased hypercontractivity.
The noise parameter is `sqrt (p * (1-p)) / 4`; after cancellation of the
normalization in the biased character, its two values are `-p / 4` and
`(1-p) / 4`. This formulation also includes the endpoint biases. -/
theorem biased_two_point_fourth_moment (p a b : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (a - p * b / 4) ^ 4 + p * (a + (1 - p) * b / 4) ^ 4 ≤
      (a ^ 2 + b ^ 2) ^ 2 := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have h1 := fourth_power_centered_bound a (-p * b / 4)
  have h2 := fourth_power_centered_bound a ((1 - p) * b / 4)
  have h3 := mul_le_mul_of_nonneg_left h1 hq
  have h4 := mul_le_mul_of_nonneg_left h2 hp
  have hvar : 0 ≤ p * (1 - p) := mul_nonneg hp hq
  have hvar1 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hpq : (1 - p) ^ 3 + p ^ 3 ≤ 1 := by nlinarith
  have hab : 0 ≤ a ^ 2 * b ^ 2 := mul_nonneg (sq_nonneg a) (sq_nonneg b)
  have hb4 : 0 ≤ b ^ 4 := by positivity
  have hvarab := mul_le_mul_of_nonneg_right hvar1 hab
  have hfour := mul_le_mul_of_nonneg_left hpq hvar
  have hfourb := mul_le_mul_of_nonneg_right hfour hb4
  have hvarb := mul_le_mul_of_nonneg_right hvar1 hb4
  nlinarith only [h3, h4, hvarab, hfourb, hvarb, hab, hb4]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.biased_two_point_fourth_moment := @_root_.OAI.Problem313.biased_two_point_fourth_moment
