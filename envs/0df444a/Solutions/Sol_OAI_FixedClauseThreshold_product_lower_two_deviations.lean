-- Prove2me | solution 1 for OAI.FixedClauseThreshold.product_lower_two_deviations
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:48:07.316674+00:00
-- url     : https://prove2.me/submissions/6a263607-b851-4761-993f-282290275f86

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Transfer.lean:L376-L393
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.product_lower_two_deviations. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer

-- ---- from OAI.Probability.RandomSAT.Transfer ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
The exact probability of distinct variables, birthday bounds, and deletion and
thinning comparisons transfer auxiliary probabilities to the proper-clause law.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem product_lower_two_deviations {κ x y a b : ℝ} (hκ : 0 ≤ κ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hax : x < 1 → κ ≤ a) (hby : y < 1 → κ ≤ b) :
    κ^2 * (1 - x - y) ≤ a * b := by
  by_cases hx1 : x < 1
  · by_cases hy1 : y < 1
    · have hprod := mul_le_mul (hax hx1) (hby hy1) hκ ha
      have hle : κ^2 * (1 - x - y) ≤ κ^2 :=
        by
          have hh : 1 - x - y ≤ 1 := by linarith
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (sq_nonneg κ)
      nlinarith
    · have hle : κ^2 * (1 - x - y) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg κ) (by linarith)
      exact hle.trans (mul_nonneg ha hb)
  · have hle : κ^2 * (1 - x - y) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg κ) (by linarith)
    exact hle.trans (mul_nonneg ha hb)

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.product_lower_two_deviations := @_root_.OAI.FixedClauseThreshold.product_lower_two_deviations
