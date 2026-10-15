-- Prove2me | solution 1 for OAI.IndependentProducts.excessConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:04:11.485506+00:00
-- url     : https://prove2.me/submissions/e517215d-7336-4b3e-b8cc-7453757827b0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean:L40-L52
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.excessConstant_pos. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds

-- ---- from OAI.Analysis.ProductSpaces.ScalarBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

lemma gaussianTail_pos (r : ℝ) : 0 < gaussianTail r := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) (measure_ne_top _ _)
  apply lt_of_lt_of_le (b := gaussianReal 0 1 (Ioo (|r| + 1) (|r| + 2)))
  · apply pos_iff_ne_zero.mpr
    intro hzero
    have hz := (gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) (by norm_num)) hzero
    have hp : (0 : ℝ≥0∞) < volume (Ioo (|r| + 1) (|r| + 2)) := by simp
    exact hp.ne' hz
  · apply measure_mono
    intro x hx
    exact le_trans (le_abs_self r) (le_trans (by linarith [hx.1]) (le_abs_self x))

lemma integrable_gaussian_abs_excess (K : ℝ) :
    Integrable (fun x : ℝ => max (|x| - 2 * K) 0) (gaussianReal 0 1) := by
  exact (((memLp_id_gaussianReal 1).integrable (by norm_num)).abs.sub (integrable_const _)).sup
    (integrable_const 0)

lemma excessConstant_pos (K : ℝ) : 0 < excessConstant K := by
  apply mul_pos (by norm_num)
  apply (integral_pos_iff_support_of_nonneg (fun x => le_max_right _ _)
    (integrable_gaussian_abs_excess K)).mpr
  apply lt_of_lt_of_le (b := gaussianReal 0 1 {x : ℝ | 2 * |K| + 1 ≤ |x|})
  · have h := gaussianTail_pos (2 * |K| + 1)
    exact ENNReal.toReal_pos_iff.mp h |>.1
  · apply measure_mono
    intro x hx
    apply Function.mem_support.mpr
    change 2 * |K| + 1 ≤ |x| at hx
    have hp : 0 < |x| - 2 * K := by nlinarith [le_abs_self K]
    exact (lt_of_lt_of_le hp (le_max_left _ _)).ne'

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

variable [IsProbabilityMeasure μ]

end SecondMoment
end IndependentProducts

namespace IndependentProducts

section GaussianSum
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

variable [Fintype ι]

end GaussianSum
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι

theorem solution (K : ℝ) : 0 < excessConstant K := by
  first
    | exact OAI.IndependentProducts.excessConstant_pos K
    | exact OAI.IndependentProducts.excessConstant_pos
    | (apply OAI.IndependentProducts.excessConstant_pos <;> assumption)
    | (intros; apply OAI.IndependentProducts.excessConstant_pos <;> assumption)
