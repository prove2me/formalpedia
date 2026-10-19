-- Prove2me | solution 1 for OAI.GaussianPropeller.SoftMin.Z_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:15:44.260014+00:00
-- url     : https://prove2.me/submissions/1a52b1f2-b0ad-4053-8967-ebb47db92684

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/SoftMinimum.lean:L62-L76
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.SoftMin.Z_fderiv. The node keeps its source
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
omit [Nonempty ι] in
lemma inner_grad [Nonempty ι] (v : ι → E) (x e : E) :
    ⟪grad v x,e⟫ = ∑ i, weight v x i*⟪v i,e⟫ := by
  simp only [grad, sum_inner, real_inner_smul_left]
lemma Z_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (Z v) (-(Z v x) • innerSL ℝ (grad v x)) x := by
  have hd (i : ι) : HasFDerivAt (fun y : E => Real.exp (-⟪v i,y⟫))
      (-Real.exp (-⟪v i,x⟫) • innerSL ℝ (v i)) x := by
    convert ((innerSL ℝ (v i)).hasFDerivAt.neg.exp) using 1 <;>
      (first | rfl | (ext y; simp))
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  convert hs using 1 <;> try rfl
  ext e
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, sum_apply,
    inner_grad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [weight]
  field_simp [ne_of_gt (Z_pos v x)]
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


theorem solution.{uE,uι} : type_of% @_root_.OAI.GaussianPropeller.SoftMin.Z_fderiv.{uE,uι} := @_root_.OAI.GaussianPropeller.SoftMin.Z_fderiv.{uE,uι}
