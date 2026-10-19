-- Prove2me | solution 2 for OAI.C0Absorption.normalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:59:30.05902+00:00
-- url     : https://prove2.me/submissions/9a808f26-31b3-43c2-be73-1b5675668440

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Triangular.lean:L114-L132
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.normalization_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular

-- ---- from OAI.Analysis.C0Absorption.Triangular ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

open Set Filter Topology
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E U Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

end
end C0Absorption

open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem normalization_bound (x y : E) :
    ‖x‖ * dist (normalize x) (normalize y) ≤ 2 * dist x y := by
  have he : ‖x‖ • (normalize x-normalize y) = x-y+(‖y‖-‖x‖) • normalize y := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖x‖ * ‖normalize x-normalize y‖ = ‖‖x‖ • (normalize x-normalize y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = ‖x-y+(‖y‖-‖x‖) • normalize y‖ := by rw [he]
    _ ≤ ‖x-y‖ + ‖(‖y‖-‖x‖) • normalize y‖ := norm_add_le _ _
    _ ≤ ‖x-y‖ + |‖y‖-‖x‖| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add_right (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (normalize_norm_le_one y) (abs_nonneg (‖y‖-‖x‖))) _
    _ ≤ ‖x-y‖+‖x-y‖ := by
      apply add_le_add_right
      simpa only [abs_sub_comm] using abs_norm_sub_norm_le x y
    _ = 2*‖x-y‖ := by ring

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open Set Filter Topology
open scoped NNReal BigOperators
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators


theorem solution : type_of% @_root_.OAI.C0Absorption.normalization_bound := @_root_.OAI.C0Absorption.normalization_bound
