-- Prove2me | solution 2 for OAI.C0Absorption.radialLift_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:01:21.259004+00:00
-- url     : https://prove2.me/submissions/5c9a2809-a5a0-4727-9ac3-e545afbdcb16

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Triangular.lean:L159-L186
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.radialLift_lipschitz. The node keeps its source
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
import Theorems.Thm_OAI_C0Absorption_normalization_bound

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

theorem norm_pointMap_le_one {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (ζ : Metric.closedBall (0 : E) 1 → Z)
    (hζ : LipschitzWith 1 ζ) (h0 : ζ zeroBall = 0) (s : Metric.closedBall (0 : E) 1) :
    ‖ζ s‖ ≤ 1 := by
  have hh := hζ.dist_le_mul s zeroBall
  rw [h0, dist_zero_right, NNReal.coe_one, one_mul] at hh
  have hb : dist s zeroBall ≤ 1 := s.property
  exact hh.trans hb

theorem radialLift_lipschitz (ζ : Metric.closedBall (0 : E) 1 → Z)
    (hζ : LipschitzWith 1 ζ) (h0 : ζ zeroBall = 0) : LipschitzWith 3 (radialLift ζ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : radialLift ζ x-radialLift ζ y =
      (‖x‖-‖y‖) • ζ (normalizedBall x) +
        ‖y‖ • (ζ (normalizedBall x)-ζ (normalizedBall y)) := by
    simp only [radialLift, sub_smul, smul_sub]
    abel
  have hdist : ‖ζ (normalizedBall x)-ζ (normalizedBall y)‖ ≤ dist (normalize x) (normalize y) := by
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, normalizedBall, dist_eq_norm, Subtype.coe_mk] using
      hζ.dist_le_mul (normalizedBall x) (normalizedBall y)
  calc
    dist (radialLift ζ x) (radialLift ζ y) = ‖radialLift ζ x-radialLift ζ y‖ := dist_eq_norm _ _
    _ ≤ |‖x‖-‖y‖|+‖y‖*dist (normalize x) (normalize y) := by
      rw [he]
      apply (norm_add_le _ _).trans
      rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
      exact add_le_add
        (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (norm_pointMap_le_one ζ hζ h0 (normalizedBall x)) (abs_nonneg (‖x‖-‖y‖)))
        (mul_le_mul_of_nonneg_left hdist (norm_nonneg y))
    _ ≤ dist x y + 2*dist x y := by
      apply add_le_add
      · simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y
      · simpa only [dist_comm] using normalization_bound y x
    _ = (3 : ℝ≥0)*dist x y := by norm_num; ring

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


theorem solution : type_of% @_root_.OAI.C0Absorption.radialLift_lipschitz := @_root_.OAI.C0Absorption.radialLift_lipschitz
