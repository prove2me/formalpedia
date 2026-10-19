-- Prove2me | solution 1 for OAI.ProjectionMoments.Weighted.measure_domination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:11:27.058921+00:00
-- url     : https://prove2.me/submissions/9cace1e1-9732-41a2-aab7-1c5002f22090

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/WeightedCover.lean:L304-L360
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.Weighted.measure_domination. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionMoments_Weighted_eval_continuousOn
import Theorems.Thm_OAI_ProjectionMoments_Weighted_finite_dual_domination

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

lemma budget_closed (b : ι → ℝ) (K : ℝ) : IsClosed (budget b K) := by
  have he : budget b K = (⋂ i, {a | 0 ≤ a i}) ∩
      (⋂ s : Finset ι, {a | ∑ i ∈ s, a i*b i ≤ K}) := by ext a; simp [budget]
  rw [he]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_iInter (fun s => isClosed_le (by fun_prop) continuous_const))

lemma budget_mem_single {b : ι → ℝ} {K : ℝ} {a : ι → ℝ} (ha : a ∈ budget b K) (i : ι) :
    a i * b i ≤ K := by
  classical
  simpa using ha.2 {i}

lemma budget_compact {b : ι → ℝ} (hb : ∀ i, 0 < b i) (K : ℝ) : IsCompact (budget b K) := by
  apply (isCompact_pi_infinite (fun i => isCompact_Icc (a := (0:ℝ)) (b := K/b i))).of_isClosed_subset
    (budget_closed b K)
  intro a ha
  exact fun i => ⟨ha.1 i, (le_div_iff₀ (hb i)).mpr (budget_mem_single ha i)⟩

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

theorem dual_domination {J : Type*} {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K) (v : J → ι → ℝ) (hv : ∀ j i, v j i ∈ Icc (0:ℝ) 1)
    (y : J → ℝ)
    (hdual : ∀ s : Finset J, ∀ c : s → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K) :
    ∃ a ∈ budget b K, ∀ j, y j ≤ ∑' i, a i*v j i := by
  classical
  let B := budget b K
  let : CompactSpace B := isCompact_iff_compactSpace.mp (budget_compact (fun i => zero_lt_one.trans_le (hb i)) K)
  let t : J → Set B := fun j => {a | y j ≤ ∑' i, a.val i*v j i}
  have hclosed : ∀ j, IsClosed (t j) := by
    intro j
    exact isClosed_le continuous_const (eval_continuousOn hb hproper hK.le (hv j)).domRestrict
  have hfinite : ∀ s : Finset J, (Set.univ ∩ ⋂ j ∈ s, t j).Nonempty := by
    intro s
    obtain ⟨a,ha,haj⟩ := finite_dual_domination hb hproper hK
      (fun j : s => v j) (fun j => hv j) (fun j : s => y j) (hdual s)
    refine ⟨⟨a,ha⟩,Set.mem_univ _,?_⟩
    simp only [Set.mem_iInter]
    intro j hj
    exact haj ⟨j,hj⟩
  obtain ⟨a,_,ha⟩ := isCompact_univ.inter_iInter_nonempty t hclosed hfinite
  exact ⟨a.val,a.property,fun j => Set.mem_iInter.mp ha j⟩

end

variable {Ω ι : Type*} [MeasurableSpace Ω]

lemma lintegral_finite_test {J : Type*} [Fintype J] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : J → Set Ω) (hS : ∀ j, MeasurableSet (S j)) (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) :
    (∫⁻ x, ∑ j, ENNReal.ofReal (c j) * (S j).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) =
      ENNReal.ofReal (∑ j, c j * μ.real (S j)) := by
  rw [lintegral_finsetSum (f := fun j x => ENNReal.ofReal (c j) * (S j).indicator (fun _ => (1 : ℝ≥0∞)) x) _ (fun j _ => measurable_const.mul (measurable_const.indicator (hS j)))]
  simp only [lintegral_const_mul _ (measurable_const.indicator (hS _))]
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hc j) (measureReal_nonneg))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ENNReal.ofReal_mul (hc j), measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [lintegral_indicator (hS j)]
  simp

theorem measure_domination [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K)
    (hdual : ∀ h : Ω → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) →
      ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*b i) ∧ (∑' i, a i*b i) ≤ K ∧
      μ ≤ Measure.sum (fun i => ENNReal.ofReal (a i) • P i) := by
  classical
  let J := {S : Set Ω // MeasurableSet S}
  let v : J → ι → ℝ := fun S i => (P i).real S
  let y : J → ℝ := fun S => μ.real S
  have hv : ∀ S i, v S i ∈ Icc (0:ℝ) 1 := by
    intro S i
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hd : ∀ s : Finset J, ∀ c : s → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K := by
    intro s c hc hci
    let h : Ω → ℝ≥0∞ := fun x => ∑ j : s,
      ENNReal.ofReal (c j) * (j.val.val).indicator (fun _ => (1:ℝ≥0∞)) x
    have hm : Measurable h := by
      exact Finset.measurable_sum _ (fun j _ => measurable_const.mul
        (measurable_const.indicator j.val.property))
    have hbnd : ∃ H : ℝ≥0, ∀ x, h x ≤ H := by
      refine ⟨∑ j : s, (c j).toNNReal, ?_⟩
      intro x
      rw [ENNReal.ofNNReal_finsetSum]
      change (∑ j : s, ENNReal.ofReal (c j) * (j.val.val).indicator (fun _ => (1:ℝ≥0∞)) x) ≤ _
      apply Finset.sum_le_sum
      intro j hj
      by_cases hx : x ∈ j.val.val <;> simp [Set.indicator, hx, ENNReal.ofReal]
    have he (ν : Measure Ω) [IsFiniteMeasure ν] : (∫⁻ x, h x ∂ν) =
        ENNReal.ofReal (∑ j : s, c j*ν.real j.val.val) :=
      lintegral_finite_test ν (fun j : s => j.val.val) (fun j => j.val.property) c hc
    have ht := hdual h hm hbnd (fun i => by rw [he]; exact ENNReal.ofReal_le_ofReal (hci i))
    rw [he, ENNReal.ofReal_le_ofReal_iff hK.le] at ht
    exact ht
  obtain ⟨a,ha,has⟩ := dual_domination hb hproper hK v hv y hd
  refine ⟨a,ha.1,cost_summable (fun i => zero_le_one.trans (hb i)) ha,
    cost_le (fun i => zero_le_one.trans (hb i)) ha,?_⟩
  apply Measure.le_iff.mpr
  intro S hS
  have hs := has ⟨S,hS⟩
  have hsum := eval_summable hb ha (hv ⟨S,hS⟩)
  have hc : ∀ i, 0 ≤ a i*(P i).real S := fun i => mul_nonneg (ha.1 i) measureReal_nonneg
  have hh := ENNReal.ofReal_le_ofReal hs
  change ENNReal.ofReal (μ.real S) ≤ ENNReal.ofReal (∑' i, a i*(P i).real S) at hh
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_tsum_of_nonneg hc hsum] at hh
  rw [Measure.sum_apply _ hS]
  convert hh using 1
  congr 1
  funext i
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (ha.1 i),
    measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end Weighted
end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments OAI.ProjectionMoments.Weighted
open scoped Topology BigOperators Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators


theorem solution : type_of% @_root_.OAI.ProjectionMoments.Weighted.measure_domination := @_root_.OAI.ProjectionMoments.Weighted.measure_domination
