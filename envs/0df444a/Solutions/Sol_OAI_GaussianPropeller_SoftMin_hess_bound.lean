-- Prove2me | solution 1 for OAI.GaussianPropeller.SoftMin.hess_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:17:15.719539+00:00
-- url     : https://prove2.me/submissions/ce9257ab-430e-400b-a10e-63520bd5d9c7

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/SoftMinimum.lean:L112-L126
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.SoftMin.hess_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum

-- ---- from OAI.Probability.GaussianPropeller.SoftMinimum ----
namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal

open Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace GaussianPropeller.SoftMin

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

lemma Z_pos (v : ι → E) (x : E) : 0 < Z v x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
lemma weight_pos (v : ι → E) (x : E) (i : ι) : 0 < weight v x i :=
  div_pos (Real.exp_pos _) (Z_pos v x)
lemma sum_weight (v : ι → E) (x : E) : ∑ i, weight v x i = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (ne_of_gt (Z_pos v x))
lemma grad_bound (v : ι → E) {L : ℝ} (hL : ∀ i, ‖v i‖ ≤ L) (x : E) : ‖grad v x‖ ≤ L := by
  calc
    ‖grad v x‖ ≤ ∑ i, ‖weight v x i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, weight v x i*L := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos v x i)]
      exact mul_le_mul_of_nonneg_left (hL i) (weight_pos v x i).le
    _ = L := by rw [← Finset.sum_mul, sum_weight, one_mul]

lemma hess_bound (v : ι → E) {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ i, ‖v i‖ ≤ L) (x : E) :
    ‖hess v x‖ ≤ 2*L^2 := by
  calc
    ‖hess v x‖ ≤ ∑ i, ‖weight v x i • ((innerSL ℝ (grad v x-v i)).smulRight (v i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, weight v x i*(2*L^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos v x i),
        ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      apply mul_le_mul_of_nonneg_left _ (weight_pos v x i).le
      have hd : ‖grad v x-v i‖ ≤ 2*L := (norm_sub_le _ _).trans (by linarith [grad_bound v hL x, hL i])
      calc
        ‖grad v x-v i‖*‖v i‖ ≤ (2*L)*L := mul_le_mul hd (hL i) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = 2*L^2 := by rw [← Finset.sum_mul, sum_weight, one_mul]

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussianPropeller.SoftMin

namespace GaussianPropeller.SoftMin
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end GaussianPropeller.SoftMin

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.SoftMin
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal


theorem solution.{uE,uι} : type_of% @_root_.OAI.GaussianPropeller.SoftMin.hess_bound.{uE,uι} := @_root_.OAI.GaussianPropeller.SoftMin.hess_bound.{uE,uι}
