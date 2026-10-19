-- Prove2me | solution 2 for OAI.ProjectionMoments.Weighted.eval_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:07:53.291986+00:00
-- url     : https://prove2.me/submissions/4261ad02-e22e-444f-b205-c23f35b079b3

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/WeightedCover.lean:L104-L130
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.Weighted.eval_continuousOn. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover

-- ---- from OAI.Probability.ProjectionMoments.WeightedCover ----
namespace OAI

noncomputable section

open scoped Topology BigOperators Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace ProjectionMoments
namespace Weighted

section
variable {ι : Type*}

lemma cost_summable {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) {K : ℝ} {a : ι → ℝ}
    (ha : a ∈ budget b K) : Summable (fun i => a i*b i) :=
  summable_of_sum_le (fun i => mul_nonneg (ha.1 i) (hb i)) ha.2

lemma cost_le {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) {K : ℝ} {a : ι → ℝ}
    (ha : a ∈ budget b K) : (∑' i, a i*b i) ≤ K :=
  (cost_summable hb ha).tsum_le_of_sum_le ha.2

lemma eval_summable {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a v : ι → ℝ}
    (ha : a ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) : Summable (fun i => a i*v i) := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (ha.1 i) (hv i).1)
    (fun i => mul_le_mul_of_nonneg_left ((hv i).2.trans (hb i)) (ha.1 i))
    (cost_summable (fun i => (zero_le_one.trans (hb i))) ha)

lemma eval_tail {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a v : ι → ℝ}
    (ha : a ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1)
    (s : Finset ι) {R : ℝ} (hR : 0 < R) (hs : ∀ i ∉ s, R ≤ b i) :
    0 ≤ (∑' i, a i*v i) - ∑ i ∈ s, a i*v i ∧
      (∑' i, a i*v i) - ∑ i ∈ s, a i*v i ≤ K/R := by
  classical
  have hc := cost_summable (fun i => zero_le_one.trans (hb i)) ha
  have he := eval_summable hb ha hv
  have hid := he.sum_add_tsum_subtype_compl s
  have hnon : 0 ≤ ∑' i : {i // i ∉ s}, a i*v i :=
    tsum_nonneg (fun i => mul_nonneg (ha.1 i) (hv i).1)
  have hcost : (∑' i : {i // i ∉ s}, a i*b i) ≤ K := by
    have heq := hc.sum_add_tsum_subtype_compl s
    have hsum : 0 ≤ ∑ i ∈ s, a i*b i :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (ha.1 i) (zero_le_one.trans (hb i)))
    have htot := cost_le (fun i => zero_le_one.trans (hb i)) ha
    linarith
  have hbound : (∑' i : {i // i ∉ s}, a i*v i) ≤ K/R := by
    calc
      _ ≤ ∑' i : {i // i ∉ s}, (a i*b i)/R := by
        apply (he.subtype _).tsum_le_tsum _ ((hc.subtype _).div_const R)
        intro i
        apply (le_div_iff₀ hR).mpr
        calc
          a i*v i*R ≤ a i*1*R :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv i).2 (ha.1 i)) hR.le
          _ ≤ a i*b i := by simpa using mul_le_mul_of_nonneg_left (hs i i.2) (ha.1 i)
      _ = (∑' i : {i // i ∉ s}, a i*b i)/R := tsum_div_const
      _ ≤ K/R := div_le_div_of_nonneg_right hcost hR.le
  constructor <;> linarith

lemma eval_continuousOn {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i)
    (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite) {K : ℝ} (hK : 0 ≤ K)
    {v : ι → ℝ} (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) :
    ContinuousOn (fun a : ι → ℝ => ∑' i, a i*v i) (budget b K) := by
  classical
  have hconv : TendstoUniformlyOn (fun s : Finset ι => fun a : ι → ℝ => ∑ i ∈ s, a i*v i)
      (fun a => ∑' i, a i*v i) atTop (budget b K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let R := (K+1)/ε
    have hR : 0 < R := by dsimp [R]; positivity
    let s := (hproper R).toFinset
    filter_upwards [eventually_ge_atTop s] with t ht
    intro a ha
    have hsmall : ∀ i ∉ t, R ≤ b i := by
      intro i hi
      apply le_of_lt
      by_contra! hh
      exact hi (ht (by simpa [s] using hh))
    have hh := eval_tail hb ha hv t hR hsmall
    rw [Real.dist_eq, abs_of_nonneg hh.1]
    apply hh.2.trans_lt
    apply (div_lt_iff₀ hR).mpr
    have he : ε*R = K+1 := by dsimp [R]; field_simp
    linarith
  apply hconv.continuousOn
  exact Filter.Eventually.frequently (Filter.Eventually.of_forall (fun _ => (by fun_prop : Continuous _).continuousOn))

end

variable {Ω ι : Type*} [MeasurableSpace Ω]

end Weighted
end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments OAI.ProjectionMoments.Weighted
open scoped Topology BigOperators Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


theorem solution : type_of% @_root_.OAI.ProjectionMoments.Weighted.eval_continuousOn := @_root_.OAI.ProjectionMoments.Weighted.eval_continuousOn
