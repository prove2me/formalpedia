-- Prove2me | solution 1 for OAI.ProjectionMoments.Weighted.finite_dual_domination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:09:33.310503+00:00
-- url     : https://prove2.me/submissions/69fe6378-5540-4655-978a-784f82c7af40

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/WeightedCover.lean:L174-L260
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.Weighted.finite_dual_domination. The node keeps its source
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

lemma budget_convex (b : ι → ℝ) (K : ℝ) : Convex ℝ (budget b K) := by
  intro a ha a' ha' t u ht hu htu
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ht (ha.1 i)) (mul_nonneg hu (ha'.1 i))
  · intro s
    have he : (∑ i ∈ s, (t • a + u • a') i * b i) =
        t*(∑ i ∈ s, a i*b i) + u*(∑ i ∈ s, a' i*b i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        mul_assoc, ← Finset.mul_sum]
    rw [he]
    calc
      _ ≤ t*K+u*K := add_le_add (mul_le_mul_of_nonneg_left (ha.2 s) ht)
        (mul_le_mul_of_nonneg_left (ha'.2 s) hu)
      _ = K := by rw [← add_mul, htu, one_mul]

lemma cost_summable {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) {K : ℝ} {a : ι → ℝ}
    (ha : a ∈ budget b K) : Summable (fun i => a i*b i) :=
  summable_of_sum_le (fun i => mul_nonneg (ha.1 i) (hb i)) ha.2

lemma eval_summable {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a v : ι → ℝ}
    (ha : a ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) : Summable (fun i => a i*v i) := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (ha.1 i) (hv i).1)
    (fun i => mul_le_mul_of_nonneg_left ((hv i).2.trans (hb i)) (ha.1 i))
    (cost_summable (fun i => (zero_le_one.trans (hb i))) ha)

lemma zero_mem_budget {b : ι → ℝ} {K : ℝ} (hK : 0 ≤ K) : (0 : ι → ℝ) ∈ budget b K := by
  constructor
  · simp
  · simpa using (fun _ : Finset ι => hK)

lemma single_mem_budget [DecidableEq ι] {b : ι → ℝ} (hb : ∀ i, 0 < b i) {K : ℝ} (hK : 0 ≤ K) (i : ι) :
    (Pi.single i (K/b i) : ι → ℝ) ∈ budget b K := by
  classical
  constructor
  · intro j
    simp only [Pi.single_apply]
    split_ifs
    · exact div_nonneg hK (hb i).le
    · exact le_rfl
  · intro s
    have he : (fun j => (Pi.single i (K/b i) : ι → ℝ) j * b j) = (Pi.single i K : ι → ℝ) := by
      ext j
      by_cases hj : j = i
      · subst j; simp [div_mul_cancel₀ K (hb i).ne']
      · simp [hj]
    rw [he]
    simp only [Pi.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hK

lemma eval_single [DecidableEq ι] {b : ι → ℝ} (K : ℝ) (i : ι) (v : ι → ℝ) :
    (∑' j, (Pi.single i (K/b i) : ι → ℝ) j * v j) = (K/b i)*v i := by
  classical
  rw [tsum_eq_single i (by intro j hj; simp [hj])]
  simp

lemma eval_smul_add {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i) {K : ℝ} {a a' v : ι → ℝ}
    (ha : a ∈ budget b K) (ha' : a' ∈ budget b K) (hv : ∀ i, v i ∈ Icc (0:ℝ) 1)
    (t u : ℝ) :
    (∑' i, (t • a + u • a') i * v i) = t*(∑' i, a i*v i)+u*(∑' i, a' i*v i) := by
  have he : (fun i => (t • a + u • a') i * v i) =
      fun i => t*(a i*v i)+u*(a' i*v i) := by ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [he, ((eval_summable hb ha hv).mul_left t).tsum_add ((eval_summable hb ha' hv).mul_left u),
    tsum_mul_left, tsum_mul_left]

lemma finite_dual_domination {J : Type*} [Fintype J] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K) (v : J → ι → ℝ) (hv : ∀ j i, v j i ∈ Icc (0:ℝ) 1)
    (y : J → ℝ)
    (hdual : ∀ c : J → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K) :
    ∃ a ∈ budget b K, ∀ j, y j ≤ ∑' i, a i*v j i := by
  classical
  let F : (ι → ℝ) → (J → ℝ) := fun a j => ∑' i, a i*v j i
  let C := F '' budget b K
  let D := C + Set.Iic (0 : J → ℝ)
  have hCc : IsCompact C := (budget_compact (fun i => zero_lt_one.trans_le (hb i)) K).image_of_continuousOn
    (continuousOn_pi.mpr (fun j => eval_continuousOn hb hproper hK.le (hv j)))
  have hCv : Convex ℝ C := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨a',ha',rfl⟩ t u ht hu htu
    refine ⟨t • a + u • a', budget_convex b K ha ha' ht hu htu, ?_⟩
    ext j
    exact eval_smul_add hb ha ha' (hv j) t u
  have hDc : IsClosed D := isClosed_Iic.add_left_of_isCompact hCc
  have hDv : Convex ℝ D := hCv.add (convex_Iic (0 : J → ℝ))
  have h00 : (0 : J → ℝ) ∈ C := ⟨0,zero_mem_budget hK.le,by ext j; simp [F]⟩
  have hneg : ∀ w : J → ℝ, w ≤ 0 → w ∈ D := by
    intro w hw
    exact ⟨0,h00,w,hw,zero_add _⟩
  have hymem : y ∈ D := by
    by_contra hy
    obtain ⟨f,U,hf,hUy⟩ := geometric_hahn_banach_closed_point hDv hDc hy
    have hU : 0 < U := by simpa using hf 0 (hneg 0 le_rfl)
    let c : J → ℝ := fun j => f (Pi.single j 1)
    have hfe (x : J → ℝ) : f x = ∑ j, c j*x j := by
      have he : x = ∑ j, x j • Pi.single j (1:ℝ) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [he, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      change x j * c j = c j * x j
      ring
    have hc : ∀ j, 0 ≤ c j := by
      intro j
      by_contra! hj
      let t := (U+1)/(-c j)
      have ht : 0 < t := div_pos (by linarith) (neg_pos.mpr hj)
      have hw : -t • Pi.single j (1:ℝ) ≤ (0 : J → ℝ) := by
        intro i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.single_apply]
        split_ifs <;> nlinarith
      have hh := hf _ (hneg _ hw)
      rw [map_smul] at hh
      change -t*c j < U at hh
      have he : -t*c j = U+1 := by dsimp [t]; field_simp [hj.ne]
      linarith
    have hsingle (i : ι) : (K/b i)*(∑ j, c j*v j i) < U := by
      have ha := single_mem_budget (fun i => zero_lt_one.trans_le (hb i)) hK.le i
      have hmem : F ((Pi.single i (K/b i) : ι → ℝ)) ∈ D :=
        ⟨F ((Pi.single i (K/b i) : ι → ℝ)),⟨_,ha,rfl⟩,0,by simp,add_zero _⟩
      have hh := hf _ hmem
      rw [hfe] at hh
      simp only [F, eval_single] at hh
      convert hh using 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have htest : ∀ i, ∑ j, (K/U*c j)*v j i ≤ b i := by
      intro i
      have hh := hsingle i
      rw [div_mul_eq_mul_div, div_lt_iff₀ (zero_lt_one.trans_le (hb i))] at hh
      have he : (∑ j, (K/U*c j)*v j i) = (K/U)*(∑ j, c j*v j i) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
      rw [he, div_mul_eq_mul_div, div_le_iff₀ hU]
      nlinarith
    have hres := hdual (fun j => K/U*c j) (fun j => mul_nonneg (div_nonneg hK.le hU.le) (hc j)) htest
    have he : (∑ j, K/U*c j*y j) = (K/U)*f y := by
      rw [hfe, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
    rw [he, div_mul_eq_mul_div, div_le_iff₀ hU] at hres
    nlinarith
  obtain ⟨z,⟨a,ha,rfl⟩,w,hw,he⟩ := hymem
  refine ⟨a,ha,?_⟩
  intro j
  have hj := congrFun he j
  have hh := hw j
  change F a j + w j = y j at hj
  change w j ≤ 0 at hh
  dsimp [F] at hj
  linarith

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


theorem solution : type_of% @_root_.OAI.ProjectionMoments.Weighted.finite_dual_domination := @_root_.OAI.ProjectionMoments.Weighted.finite_dual_domination
