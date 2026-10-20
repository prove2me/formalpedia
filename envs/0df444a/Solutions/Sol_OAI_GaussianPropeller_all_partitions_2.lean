-- Prove2me | solution 2 for OAI.GaussianPropeller.all_partitions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:29:04.976552+00:00
-- url     : https://prove2.me/submissions/494add24-da20-44dd-8b0f-22e74e4aa393

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Main.lean:L78-L82
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.GaussianPropeller.all_partitions.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_GaussianPropeller_all_partitions) verbatim and is proved by it.
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
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_Scalar
import Definitions.Def_OAI_Probability_GaussianPropeller_Configuration
import Theorems.Thm_OAI_GaussianPropeller_Reduction_Configuration_impossible_five_or_more
import Theorems.Thm_OAI_GaussianPropeller_Reduction_append_empty_partition
import Theorems.Thm_OAI_GaussianPropeller_OneCell_normalized_cell_probability
import Theorems.Thm_OAI_GaussianPropeller_ProbabilityBounds_linear_quadratic_of_loss
import Theorems.Thm_OAI_GaussianPropeller_Reduction_active_probability_mem
import Theorems.Thm_OAI_GaussianPropeller_Reduction_minimal_cap_four
import Theorems.Thm_OAI_GaussianPropeller_Reduction_minimal_cap_three
import Theorems.Thm_OAI_GaussianPropeller_Reduction_minimal_loss_constraint
import Theorems.Thm_OAI_GaussianPropeller_Reduction_normalized_centroid_lt_two_thirds
import Theorems.Thm_OAI_GaussianPropeller_Reduction_normalized_tuple_pair
import Theorems.Thm_OAI_GaussianPropeller_sum_centroid_eq_zero
import Theorems.Thm_OAI_GaussianPropeller_Reduction_exists_unique_scoreCell
import Theorems.Thm_OAI_GaussianPropeller_Reduction_four_incompatibility
import Theorems.Thm_OAI_GaussianPropeller_Reduction_gaussian_hyperplane_null
import Theorems.Thm_OAI_GaussianPropeller_Reduction_pairing_le_width
import Theorems.Thm_OAI_GaussianPropeller_Reduction_partition_bound_small
import Theorems.Thm_OAI_GaussianPropeller_Reduction_remove_null_partition
import Theorems.Thm_OAI_GaussianPropeller_Reduction_sectorScores_norms
import Theorems.Thm_OAI_GaussianPropeller_Reduction_width_three

-- ---- from OAI.Probability.GaussianPropeller.Moments ----
namespace OAI

universe uF

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller

open scoped RealInnerProductSpace

theorem integrable_id_gaussian (d : ℕ) :
    Integrable (fun x : Space d => x) (gaussian d) := by
  exact IsGaussian.integrable_id (μ := stdGaussian (Space d))

theorem integrable_id_restrict (d : ℕ) (A : Set (Space d)) :
    Integrable (fun x : Space d => x) ((gaussian d).restrict A) :=
  (integrable_id_gaussian d).restrict

theorem value_nonneg {d k : ℕ} (A : Fin k → Set (Space d)) : 0 ≤ value A := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖centroid (A i)‖)

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Dual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

theorem le_scoreMax (v : Fin k → Space d) (i : Fin k) (x : Space d) :
    ⟪v i, x⟫ ≤ scoreMax v x := by
  exact Finset.le_sup' (fun j => ⟪v j, x⟫) (Finset.mem_univ i)

theorem scoreMax_le_iff (v : Fin k → Space d) (x : Space d) (b : ℝ) :
    scoreMax v x ≤ b ↔ ∀ i, ⟪v i, x⟫ ≤ b := by
  simp only [scoreMax, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

theorem exists_scoreMax (v : Fin k → Space d) (x : Space d) :
    ∃ i, ⟪v i, x⟫ = scoreMax v x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)
  exact ⟨i, hi.symm⟩

theorem continuous_scoreMax (v : Fin k → Space d) : Continuous (scoreMax v) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun _ _ => by fun_prop)

theorem norm_scoreMax_le (v : Tuple d k) (x : Space d) :
    ‖scoreMax v.ofLp x‖ ≤ ‖v‖ * ‖x‖ := by
  obtain ⟨i, hi⟩ := exists_scoreMax v.ofLp x
  rw [← hi]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg x))

theorem integrable_scoreMax (v : Tuple d k) :
    Integrable (scoreMax v.ofLp) (gaussian d) := by
  apply ((integrable_id_gaussian d).norm.const_mul ‖v‖).mono'
    (continuous_scoreMax v.ofLp).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_scoreMax_le v)

theorem scoreMax_sub_le (v w : Tuple d k) (x : Space d) :
    scoreMax v.ofLp x - scoreMax w.ofLp x ≤ ‖v - w‖ * ‖x‖ := by
  rw [sub_le_iff_le_add]
  apply (scoreMax_le_iff _ _ _).mpr
  intro i
  have hinner := real_inner_le_norm (v.ofLp i - w.ofLp i) x
  have hcoord : ‖v.ofLp i - w.ofLp i‖ ≤ ‖v - w‖ := PiLp.norm_apply_le (v - w) i
  have hmul := mul_le_mul_of_nonneg_right hcoord (norm_nonneg x)
  rw [inner_sub_left] at hinner
  linarith [le_scoreMax w.ofLp i x]

theorem norm_scoreMax_sub_le (v w : Tuple d k) (x : Space d) :
    ‖scoreMax v.ofLp x - scoreMax w.ofLp x‖ ≤ ‖v - w‖ * ‖x‖ := by
  rw [Real.norm_eq_abs, abs_le]
  have h := scoreMax_sub_le w v x
  rw [norm_sub_rev] at h
  exact ⟨by linarith, scoreMax_sub_le v w x⟩

theorem width_lipschitz_bound (v w : Tuple d k) :
    ‖width v - width w‖ ≤ (∫ x : Space d, ‖x‖ ∂gaussian d) * ‖v - w‖ := by
  rw [width, width, ← integral_sub (integrable_scoreMax v) (integrable_scoreMax w)]
  calc
    ‖∫ x, scoreMax v.ofLp x - scoreMax w.ofLp x ∂gaussian d‖ ≤
        ∫ x : Space d, ‖v - w‖ * ‖x‖ ∂gaussian d :=
      norm_integral_le_of_norm_le ((integrable_id_gaussian d).norm.const_mul _)
        (Filter.Eventually.of_forall (norm_scoreMax_sub_le v w))
    _ = (∫ x : Space d, ‖x‖ ∂gaussian d) * ‖v - w‖ := by
      rw [integral_const_mul, mul_comm]

theorem continuous_width : Continuous (width : Tuple d k → ℝ) := by
  let K : NNReal := ⟨∫ x : Space d, ‖x‖ ∂gaussian d,
    integral_nonneg (fun x => norm_nonneg x)⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) ?_).continuous
  intro v w
  change ‖width v - width w‖ ≤ (∫ x : Space d, ‖x‖ ∂gaussian d) * ‖v - w‖
  exact width_lipschitz_bound v w

omit [NeZero k] in
theorem measurable_scoreCell (v : Fin k → Space d) (i : Fin k) :
    MeasurableSet (scoreCell v i) := by
  change MeasurableSet ({x | ∀ j, ⟪v j, x⟫ ≤ ⟪v i, x⟫} ∩
    {x | ∀ j, j < i → ⟪v j, x⟫ < ⟪v i, x⟫})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    by_cases h : j < i
    · simpa [h] using
        (measurableSet_lt (show Measurable (fun x : Space d => ⟪v j, x⟫) by fun_prop)
          (show Measurable (fun x : Space d => ⟪v i, x⟫) by fun_prop))
    · simp [h]

theorem scoreCell_partition (v : Fin k → Space d) : IsPartition (scoreCell v) :=
  ⟨measurable_scoreCell v, Filter.Eventually.of_forall (exists_unique_scoreCell v)⟩

theorem scoreCell_score (v : Fin k → Space d) {i : Fin k} {x : Space d}
    (hx : x ∈ scoreCell v i) : ⟪v i, x⟫ = scoreMax v x := by
  exact le_antisymm (le_scoreMax v i x) ((scoreMax_le_iff _ _ _).mpr hx.1)

omit [NeZero k] in
theorem norm_moments_sq (A : Fin k → Set (Space d)) : ‖moments A‖ ^ 2 = value A :=
  PiLp.norm_sq_eq_of_L2 _ _

omit [NeZero k] in
theorem pairing_integral {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) :
    ⟪v, moments A⟫ = ∫ x, ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x
      ∂gaussian d := by
  rw [PiLp.inner_apply, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (hA.1 i), integral_inner (integrable_id_restrict d (A i))]
    rfl
  · intro i _
    exact ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1 i)

theorem pairing_scoreCell (v : Tuple d k) :
    ⟪v, moments (scoreCell v.ofLp)⟫ = width v := by
  classical
  rw [pairing_integral (scoreCell_partition v.ofLp)]
  apply integral_congr_ae
  filter_upwards [] with x
  obtain ⟨i, hi, huniq⟩ := exists_unique_scoreCell v.ofLp x
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using scoreCell_score v.ofLp hi
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

theorem width_nonneg (v : Tuple d k) : 0 ≤ width v := by
  let i : Fin k := ⟨0, NeZero.pos k⟩
  have h := integral_mono_ae ((integrable_id_gaussian d).const_inner (v.ofLp i))
    (integrable_scoreMax v) (Filter.Eventually.of_forall (le_scoreMax v.ofLp i))
  have hzero : (∫ x : Space d, x ∂gaussian d) = 0 := integral_id_stdGaussian
  rw [integral_inner (integrable_id_gaussian d), hzero, inner_zero_right] at h
  exact h

theorem exists_max_width [NeZero d] :
    ∃ v : Tuple d k, ‖v‖ = 1 ∧ ∀ w : Tuple d k, ‖w‖ = 1 → width w ≤ width v := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : Tuple d k) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
    continuous_width.continuousOn
  refine ⟨v, ?_, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using hv
  · intro w hw
    apply hmax
    simpa only [Metric.mem_sphere, dist_zero_right] using hw

theorem norm_moments_le {v : Tuple d k}
    (hmax : ∀ w : Tuple d k, ‖w‖ = 1 → width w ≤ width v)
    {A : Fin k → Set (Space d)} (hA : IsPartition A) : ‖moments A‖ ≤ width v := by
  by_cases hz : moments A = 0
  · simpa only [hz, norm_zero] using width_nonneg v
  have hn : ‖moments A‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let w : Tuple d k := ‖moments A‖⁻¹ • moments A
  have hw : ‖w‖ = 1 := by
    rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]
  have h := (pairing_le_width hA w).trans (hmax w hw)
  have heq : ⟪w, moments A⟫ = ‖moments A‖ := by
    dsimp [w]
    rw [inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    field_simp
  rwa [heq] at h

theorem exists_optimal_partition [NeZero d] :
    ∃ A : Fin k → Set (Space d), IsPartition A ∧
      ∀ B : Fin k → Set (Space d), IsPartition B → value B ≤ value A := by
  obtain ⟨v, hv, hmax⟩ := exists_max_width (d := d) (k := k)
  let A := scoreCell v.ofLp
  have hA := scoreCell_partition v.ofLp
  have hnorm : ‖moments A‖ = width v := by
    apply le_antisymm (norm_moments_le hmax hA)
    rw [← pairing_scoreCell]
    simpa only [hv, one_mul] using real_inner_le_norm v (moments A)
  refine ⟨A, hA, ?_⟩
  intro B hB
  have hnormB := norm_moments_le hmax hB
  rw [← hnorm] at hnormB
  rw [← norm_moments_sq, ← norm_moments_sq]
  exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hnormB

theorem exists_minimal_optimal [NeZero d] :
    ∃ A : Fin k → Set (Space d), MinimalOptimal A := by
  classical
  have hex : ∃ n, ∃ A : Fin k → Set (Space d), Optimal A ∧ activeCount A = n := by
    obtain ⟨A, hA⟩ := exists_optimal_partition (d := d) (k := k)
    exact ⟨activeCount A, A, hA, rfl⟩
  obtain ⟨A, hA, hn⟩ := Nat.find_spec hex
  refine ⟨A, hA, ?_⟩
  intro B hB
  rw [hn]
  exact Nat.find_min' hex ⟨B, hB, rfl⟩

omit [NeZero k] in
theorem centroid_eq_zero_of_null {A : Set (Space d)} (hA : gaussian d A = 0) : centroid A = 0 := by
  unfold centroid
  rw [Measure.restrict_eq_zero.mpr hA, integral_zero_measure]

omit [NeZero k] in
theorem measurableSet_closedCell (z : Fin k → Space d) (i : Fin k) :
    MeasurableSet (closedCell z i) := by
  unfold closedCell
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => measurableSet_le
    (by fun_prop) (by fun_prop))

end Reduction

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Attainment ----
namespace OAI

universe uE

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem perimeter_sq_le {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : (‖a-b‖ + ‖a-c‖ + ‖b-c‖)^2 ≤
      9 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
  have hcs : (‖a-b‖ + ‖a-c‖ + ‖b-c‖)^2 ≤
      3 * (‖a-b‖^2 + ‖a-c‖^2 + ‖b-c‖^2) := by
    nlinarith [sq_nonneg (‖a-b‖ - ‖a-c‖), sq_nonneg (‖a-b‖ - ‖b-c‖),
      sq_nonneg (‖a-c‖ - ‖b-c‖)]
  have hid : ‖a-b‖^2 + ‖a-c‖^2 + ‖b-c‖^2 =
      3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) - ‖a+b+c‖^2 := by
    simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left]
    ring
  rw [hid] at hcs
  nlinarith [sq_nonneg ‖a+b+c‖]

theorem width_three_sq_le {d : ℕ} (v : Tuple d 3) :
    (width v)^2 ≤ (9 / (8 * Real.pi)) * ‖v‖^2 := by
  have hp := perimeter_sq_le (v.ofLp 0) (v.ofLp 1) (v.ofLp 2)
  have hnorm : ‖v‖^2 = ‖v.ofLp 0‖^2 + ‖v.ofLp 1‖^2 + ‖v.ofLp 2‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  rw [← hnorm] at hp
  rw [width_three, div_pow]
  have hs : (2 * Real.sqrt (2 * Real.pi))^2 = 8 * Real.pi := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [hs]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * Real.pi)).mpr
  calc
    _ ≤ 9 * ‖v‖^2 := hp
    _ = 9 / (8 * Real.pi) * ‖v‖^2 * (8 * Real.pi) := by
      field_simp

theorem three_partition_bound {d : ℕ} {A : Fin 3 → Set (Space d)} (hA : IsPartition A) :
    value A ≤ 9 / (8 * Real.pi) := by
  have hpair : value A ≤ width (moments A) := by
    simpa only [real_inner_self_eq_norm_sq, norm_moments_sq] using
      pairing_le_width hA (moments A)
  have hsq := width_three_sq_le (moments A)
  rw [norm_moments_sq] at hsq
  have hn := value_nonneg A
  have hw : 0 ≤ width (moments A) := hn.trans hpair
  have hval := (sq_le_sq₀ hn hw).mpr hpair
  have hB : (0 : ℝ) < 9 / (8 * Real.pi) := by positivity
  nlinarith

theorem centroid_congr_ae {d : ℕ} {A B : Set (Space d)}
    (h : A =ᵐ[gaussian d] B) : centroid A = centroid B := by
  exact setIntegral_congr_set h

theorem value_congr_ae {d k : ℕ} {A B : Fin k → Set (Space d)}
    (h : ∀ i, A i =ᵐ[gaussian d] B i) : value A = value B := by
  apply Finset.sum_congr rfl
  intro i _
  rw [centroid_congr_ae (h i)]

theorem partition_congr_ae {d k : ℕ} {A B : Fin k → Set (Space d)}
    (hA : IsPartition A) (hB : ∀ i, MeasurableSet (B i))
    (h : ∀ i, A i =ᵐ[gaussian d] B i) : IsPartition B := by
  refine ⟨hB, ?_⟩
  have hh := ae_all_iff.mpr h
  filter_upwards [hA.2, hh] with x hx heq
  change ∀ i, (x ∈ A i) = (x ∈ B i) at heq
  obtain ⟨i, hi, hu⟩ := hx
  exact ⟨i, Eq.mp (heq i) hi, fun j hj => hu j (Eq.mpr (heq j) hj)⟩

theorem closedCell_eq_scoreCell_ae {d k : ℕ} (v : Fin k → Space d)
    (hv : Function.Injective v) (i : Fin k) :
    closedCell v i =ᵐ[gaussian d] scoreCell v i := by
  have ht (j : Fin k) (hij : i ≠ j) : ∀ᵐ x ∂gaussian d, ⟪v i, x⟫ ≠ ⟪v j, x⟫ := by
    rw [ae_iff]
    simpa only [not_not, inner_sub_left, sub_eq_zero] using
      gaussian_hyperplane_null (v i - v j) (sub_ne_zero.mpr (hv.ne hij)) 0
  have ht' := ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun hij => ht j hij))
  filter_upwards [ht'] with x hx
  apply propext
  constructor
  · intro hc
    refine ⟨hc, fun j hji => ?_⟩
    exact lt_of_le_of_ne (hc j) (Ne.symm (hx j (ne_of_gt hji)))
  · exact fun hc => hc.1

theorem sectorScores_scores (d : ℕ) (hd : 2 ≤ d) (x : Space d) :
    ⟪(sectorScores d hd).ofLp 0, x⟫ = 2 * Real.sqrt 3 * coord 0 x ∧
    ⟪(sectorScores d hd).ofLp 1, x⟫ = -Real.sqrt 3 * coord 0 x + 3 * coord 1 x ∧
    ⟪(sectorScores d hd).ofLp 2, x⟫ = -Real.sqrt 3 * coord 0 x - 3 * coord 1 x := by
  simp [sectorScores, axis0, axis1, coord, show 0 < d by omega, show 1 < d by omega,
    inner_add_left, inner_sub_left, inner_smul_left, EuclideanSpace.inner_single_left]

theorem sectorScores_closed (d : ℕ) (hd : 2 ≤ d) (i : Fin 3) :
    closedCell (sectorScores d hd).ofLp i = propeller d 3 i := by
  ext x
  obtain ⟨h0, h1, h2⟩ := sectorScores_scores d hd x
  fin_cases i <;>
    simp [closedCell, propeller, Fin.forall_fin_succ, h0, h1, h2, abs_le] <;>
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith

theorem sectorScores_injective (d : ℕ) (hd : 2 ≤ d) :
    Function.Injective (sectorScores d hd).ofLp := by
  obtain ⟨_, h01, h02, h12⟩ := sectorScores_norms d hd
  intro i j hij
  have hz : ‖(sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j‖ = 0 := by
    rw [hij, sub_self, norm_zero]
  fin_cases i <;> fin_cases j <;> simp_all [norm_sub_rev]

theorem propeller_three (d : ℕ) (hd : 2 ≤ d) :
    IsPartition (propeller d 3) ∧ value (propeller d 3) = 9 / (8 * Real.pi) := by
  let v := sectorScores d hd
  have he (i : Fin 3) : propeller d 3 i =ᵐ[gaussian d] scoreCell v.ofLp i := by
    rw [← sectorScores_closed d hd i]
    exact closedCell_eq_scoreCell_ae v.ofLp (sectorScores_injective d hd) i
  have hp : IsPartition (propeller d 3) :=
    partition_congr_ae (scoreCell_partition v.ofLp)
      (fun i => by rw [← sectorScores_closed d hd i]; exact measurableSet_closedCell _ i)
      (fun i => (he i).symm)
  refine ⟨hp, le_antisymm (three_partition_bound hp) ?_⟩
  rw [value_congr_ae he]
  obtain ⟨hv, h01, h02, h12⟩ := sectorScores_norms d hd
  have hw : (width v)^2 = 36 * (9 / (8 * Real.pi)) := by
    rw [width_three, h01, h02, h12, div_pow, mul_pow,
      Real.sq_sqrt (by positivity)]
    field_simp; ring
  have hcs := norm_inner_le_norm (𝕜 := ℝ) v (moments (scoreCell v.ofLp))
  rw [pairing_scoreCell, Real.norm_eq_abs] at hcs
  have hs := (sq_le_sq₀ (abs_nonneg (width v))
    (mul_nonneg (norm_nonneg v) (norm_nonneg (moments (scoreCell v.ofLp))))).mpr hcs
  rw [sq_abs, mul_pow, norm_moments_sq, hw] at hs
  change 36 * (9 / (8 * Real.pi)) ≤ ‖sectorScores d hd‖^2 * _ at hs
  rw [hv] at hs
  linarith only [hs]

theorem append_empty_value {d k : ℕ} (A : Fin k → Set (Space d)) :
    value (Fin.lastCases ∅ A) = value A := by
  simp [value, Fin.sum_univ_castSucc]

theorem propeller_succ (d k : ℕ) (hk : 3 ≤ k) :
    propeller d (k+1) = Fin.lastCases ∅ (propeller d k) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [propeller, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
  · simp [propeller]

theorem propeller_attainment (d k : ℕ) (hd : 2 ≤ d) (hk : 3 ≤ k) :
    IsPartition (propeller d k) ∧ value (propeller d k) = 9 / (8 * Real.pi) := by
  induction k, hk using Nat.le_induction with
  | base => exact propeller_three d hd
  | succ k hk ih =>
    rw [propeller_succ d k hk]
    exact ⟨append_empty_partition ih.1, (append_empty_value _).trans ih.2⟩

end GaussianPropeller.Reduction

namespace GaussianPropeller

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Elimination ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction.Configuration
variable {d k:ℕ}

lemma impossible_four (D:Configuration d 4) : False :=
  four_incompatibility D.z D.P D.zero D.norm D.pos D.order D.obtuse D.cap
    D.probability D.half (D.cap3 rfl) D.linear (D.loss4 rfl) D.pair

end GaussianPropeller.Reduction.Configuration

namespace GaussianPropeller.Reduction
variable {d k:ℕ}

lemma remove_null_value {A:Fin (k+1)→Set (Space d)} (i:Fin (k+1))
    (hi:gaussian d (A i)=0) : value (fun j:Fin k=>A (i.succAbove j))=value A := by
  unfold value
  rw [Fin.sum_univ_succAbove (fun j=>‖centroid (A j)‖^2) i,centroid_eq_zero_of_null hi]
  simp

end GaussianPropeller.Reduction

end OAI

-- ---- inlined from the OAI_GaussianPropeller_Reduction_exists_configuration solution (the platform cannot check that node's statement) ----
-- ---- from OAI.Probability.GaussianPropeller.Moments ----
namespace OAI

universe uF

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller

open scoped RealInnerProductSpace


theorem sum_indicator_eq {d k : ℕ} {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {F : Type uF} [AddCommMonoid F] (f : Space d → F) :
    (fun x => ∑ i, (A i).indicator f x) =ᵐ[gaussian d] f := by
  classical
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, huniq⟩ := hx
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi f
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) f
  · simp

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Dual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem merge_partition {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) : IsPartition (merge A i j) := by
  classical
  constructor
  · intro l
    by_cases hli : l = i
    · simpa [merge, hli] using (hA.1 i).union (hA.1 j)
    · by_cases hlj : l = j
      · simp [merge, hlj, hij.symm]
      · simpa [merge, hli, hlj] using hA.1 l
  · filter_upwards [hA.2] with x hx
    obtain ⟨l, hl, huniq⟩ := hx
    by_cases hlj : l = j
    · subst l
      refine ⟨i, ?_, ?_⟩
      · simp [merge, hl]
      · intro q hq
        by_cases hqi : q = i
        · exact hqi
        · by_cases hqj : q = j
          · simp [merge, hqj, hij.symm] at hq
          · have hqA : x ∈ A q := by simpa [merge, hqi, hqj] using hq
            exact False.elim (hqj (huniq q hqA))
    · refine ⟨l, ?_, ?_⟩
      · by_cases hli : l = i
        · subst l
          simp [merge, hl]
        · simp [merge, hli, hlj, hl]
      · intro q hq
        by_cases hqi : q = i
        · subst q
          have h : x ∈ A i ∨ x ∈ A j := by simpa [merge] using hq
          rcases h with hi | hj
          · exact huniq i hi
          · exact False.elim (hlj (huniq j hj).symm)
        · by_cases hqj : q = j
          · simp [merge, hqj, hij.symm] at hq
          · apply huniq q
            simpa [merge, hqi, hqj] using hq

omit [NeZero k] in
theorem centroid_union {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) : centroid (A i ∪ A j) = centroid (A i) + centroid (A j) := by
  have hind : (A i ∪ A j).indicator (fun x => x) =ᵐ[gaussian d]
      (fun x => (A i).indicator (fun x => x) x + (A j).indicator (fun x => x) x) := by
    filter_upwards [hA.2] with x hx
    obtain ⟨l, _, huniq⟩ := hx
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j
    · exact False.elim (hij ((huniq i hi).trans (huniq j hj).symm))
    all_goals simp [Set.indicator, hi, hj]
  unfold centroid
  rw [← integral_indicator ((hA.1 i).union (hA.1 j)), integral_congr_ae hind,
    integral_add ((integrable_id_gaussian d).indicator (hA.1 i))
      ((integrable_id_gaussian d).indicator (hA.1 j)),
    integral_indicator (hA.1 i), integral_indicator (hA.1 j)]

omit [NeZero k] in
theorem value_merge {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) :
    value (merge A i j) = value A + 2 * ⟪centroid (A i), centroid (A j)⟫ := by
  classical
  have hcent : centroid (A i ∪ A j) = centroid (A i) + centroid (A j) := centroid_union hA hij
  have hfun (l : Fin k) : ‖centroid (merge A i j l)‖ ^ 2 =
      ‖centroid (A l)‖ ^ 2 +
      (if l = i then ‖centroid (A i) + centroid (A j)‖ ^ 2 - ‖centroid (A i)‖ ^ 2 else 0) +
      (if l = j then -‖centroid (A j)‖ ^ 2 else 0) := by
    by_cases hli : l = i
    · subst l
      simp [merge, hij, hcent]
    · by_cases hlj : l = j
      · subst l
        simp [merge, hij.symm]
      · simp [merge, hli, hlj]
  unfold value
  simp_rw [hfun, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [norm_add_sq_real]
  ring

omit [NeZero k] in
theorem activeCount_merge_lt {A : Fin k → Set (Space d)} {i j : Fin k}
    (hij : i ≠ j) (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0) :
    activeCount (merge A i j) < activeCount A := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro l hl
    simp only [activeLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    by_cases hli : l = i
    · simpa only [hli] using hi
    · by_cases hlj : l = j
      · simp [merge, hlj, hij.symm] at hl
      · simpa only [merge, ite_eq_right hli, ite_eq_right hlj] using hl
  · intro heq
    have hs : j ∈ activeLabels (merge A i j) := by
      rw [heq]
      simpa only [activeLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have hnon : gaussian d (merge A i j j) ≠ 0 := (Finset.mem_filter.mp hs).2
    exact hnon (by simp [merge, hij.symm])

omit [NeZero k] in
theorem negative_inner_of_minimal {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    {i j : Fin k} (hij : i ≠ j) (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0) :
    ⟪centroid (A i), centroid (A j)⟫ < 0 := by
  have hpart := merge_partition hA.1.1 hij
  have hvalue := value_merge hA.1.1 hij
  have hbound := hA.1.2 _ hpart
  have hle : ⟪centroid (A i), centroid (A j)⟫ ≤ 0 := by linarith
  apply lt_of_le_of_ne hle
  intro heq
  have heqval : value (merge A i j) = value A := by rw [heq, mul_zero, add_zero] at hvalue; exact hvalue
  have hopt : Optimal (merge A i j) := ⟨hpart, fun B hB => by rw [heqval]; exact hA.1.2 B hB⟩
  exact (not_lt_of_ge (hA.2 _ hopt)) (activeCount_merge_lt hij hi hj)


omit [NeZero k] in

theorem two_nonzero_centroids {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (hpos : 0 < value A) : ∃ i j, i ≠ j ∧ centroid (A i) ≠ 0 ∧ centroid (A j) ≠ 0 := by
  classical
  have hi : ∃ i, centroid (A i) ≠ 0 := by
    by_contra! h
    have hz : value A = 0 := by simp [value, h]
    linarith
  obtain ⟨i, hi⟩ := hi
  have hj : ∃ j, j ≠ i ∧ centroid (A j) ≠ 0 := by
    by_contra! h
    have hz : ∑ j, centroid (A j) = centroid (A i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact h j hji
      · simp
    exact hi (hz.symm.trans (sum_centroid_eq_zero hA))
  obtain ⟨j, hji, hj⟩ := hj
  exact ⟨i, j, hji.symm, hi, hj⟩

omit [NeZero k] in
theorem active_centroid_ne_zero {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i : Fin k} (hi : gaussian d (A i) ≠ 0) : centroid (A i) ≠ 0 := by
  obtain ⟨j, l, hjl, hj, hl⟩ := two_nonzero_centroids hA.1.1 hpos
  have hjm : gaussian d (A j) ≠ 0 := fun hz => hj (centroid_eq_zero_of_null hz)
  have hlm : gaussian d (A l) ≠ 0 := fun hz => hl (centroid_eq_zero_of_null hz)
  by_cases hij : i = j
  · simpa only [hij] using hj
  · have hneg := negative_inner_of_minimal hA hij hi hjm
    intro hz
    simp only [hz, inner_zero_left] at hneg
    exact (lt_irrefl 0) hneg

end Reduction

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CellBounds ----
namespace OAI

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction
open Set GaussianPropeller.Quantile GaussianPropeller.OneCell GaussianPropeller.ProbabilityBounds
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

lemma minimal_universal_loss (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    ∃ x ≥ (0:ℝ), p x=(gaussian d).real (A i) ∧
      (9/(8*Real.pi))*(‖centroid (A i)‖/Real.sqrt (value A))^2 /
      (1+Real.sqrt (1-(‖centroid (A i)‖/Real.sqrt (value A))^2)) ≤ loss x := by
  obtain ⟨x,hx,hp,hl⟩ := minimal_loss_constraint hk hA hC hall i
  refine ⟨x,hx,hp, le_trans ?_ hl⟩
  have hCp : 0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hC.le (sq_nonneg _)) (by positivity)
  apply add_le_add_right
  apply Real.sqrt_le_sqrt
  have hk1 : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hα : 1≤(k:ℝ)/((k:ℝ)-1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  nlinarith only [mul_nonneg (sub_nonneg.mpr hα) (sq_nonneg (‖centroid (A i)‖/Real.sqrt (value A)))]

lemma minimal_linear_quadratic (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    0.415*(‖centroid (A i)‖/Real.sqrt (value A))+
      0.15*(‖centroid (A i)‖/Real.sqrt (value A))^2 < (gaussian d).real (A i) := by
  have hCp : 0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  obtain ⟨x,hx,hp,hl⟩ := minimal_universal_loss hk hA hC hall i
  rw [← hp]
  exact linear_quadratic_of_loss (div_pos (norm_pos_iff.mpr (active_centroid_ne_zero hA hCp (hall i)))
      (Real.sqrt_pos.mpr hCp)) (normalized_centroid_lt_two_thirds (hA.1.1.1 i) hC).le hx hl

end GaussianPropeller.Reduction

end OAI

-- ---- from OAI.Probability.GaussianPropeller.SpanReduction ----
namespace OAI

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem sum_cell_probability {A : Fin k → Set (Space d)} (hA : IsPartition A) :
    ∑ i, (gaussian d).real (A i) = 1 := by
  let : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  have hsum := integral_congr_ae (sum_indicator_eq hA (fun _ => (1:ℝ)))
  rw [integral_finsetSum] at hsum
  · simpa only [integral_indicator_const (1:ℝ) (hA.1 _), smul_eq_mul, mul_one,
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hsum
  · intro i _
    exact (integrable_const (1:ℝ)).indicator (hA.1 i)

end GaussianPropeller.Reduction

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Configuration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell ProbabilityBounds
open scoped RealInnerProductSpace

variable {d k:ℕ} [NeZero k]

lemma exists_configuration (hk:2≤k) {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0) :
    Nonempty (Configuration d k) := by
  classical
  have hCp:0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hs:0<(Real.sqrt (value A))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hCp)
  let v:Fin k→Space d := fun j=>(Real.sqrt (value A))⁻¹•centroid (A j)
  let σ:=_root_.Tuple.sort (fun j=> -‖v j‖)
  let z:Fin k→Space d := fun j=>v (σ j)
  let P:Fin k→ℝ := fun j=>(gaussian d).real (A (σ j))
  have hr:∀ j,‖v j‖=‖centroid (A j)‖/Real.sqrt (value A) := by
    intro j
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    ring
  have hz:∀ j,‖z j‖=‖centroid (A (σ j))‖/Real.sqrt (value A) := fun j=>hr (σ j)
  refine ⟨{z:=z,P:=P,zero:=?_,norm:=?_,pos:=?_,order:=?_,obtuse:=?_,cap:=?_,
            probability:=?_,half:=?_,quadratic:=?_,linear:=?_,pair:=?_,cap3:=?_,loss4:=?_}⟩
  · dsimp [z]
    rw [Equiv.sum_comp σ]
    simp only [v,←Finset.smul_sum,sum_centroid_eq_zero hA.1.1,smul_zero]
  · dsimp [z]
    rw [Equiv.sum_comp σ (fun j => ‖v j‖^2)]
    simp_rw [hr,div_pow,Real.sq_sqrt hCp.le]
    rw [←Finset.sum_div]
    change value A/value A=1
    exact div_self hCp.ne'
  · intro j
    exact smul_ne_zero hs.ne' (active_centroid_ne_zero hA hCp (hall (σ j)))
  · intro i j hij
    have hh:=_root_.Tuple.monotone_sort (fun j=> -‖v j‖) hij
    exact neg_le_neg_iff.mp hh
  · intro i j hij
    change ⟪(Real.sqrt (value A))⁻¹•centroid (A (σ i)),(Real.sqrt (value A))⁻¹•centroid (A (σ j))⟫<0
    rw [real_inner_smul_left,real_inner_smul_right]
    exact mul_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg hs
      (negative_inner_of_minimal hA (σ.injective.ne hij) (hall _) (hall _)))
  · intro j
    rw [hz]
    exact (normalized_centroid_lt_two_thirds (hA.1.1.1 _) hC).le
  · dsimp [P]
    rw [Equiv.sum_comp σ (fun j => (gaussian d).real (A j))]
    exact sum_cell_probability hA.1.1
  · intro j
    exact (active_probability_mem hk hA hCp (hall (σ j))).2
  · intro j
    rw [hz]
    by_cases hk5:k=5
    · subst k
      convert minimal_cap_four hA hC hall (σ j) using 1
      norm_num [P]
    · simp only [ite_eq_right hk5]
      convert normalized_cell_probability (hA.1.1.1 (σ j)) hC using 1 <;>
        norm_num [P,centroid,gaussian]
  · intro j
    rw [hz]
    exact (minimal_linear_quadratic hk hA hC hall (σ j)).le
  · intro i j l hij hil
    exact normalized_tuple_pair hA hC hall (σ.injective.ne hij) (σ.injective.ne hil)
  · intro hk4 j
    subst k
    rw [hz]
    exact minimal_cap_three hA hC hall (σ j)
  · intro hk4 j
    subst k
    rw [hz]
    obtain ⟨x,hx,hpx,hl⟩:=minimal_loss_constraint (by norm_num) hA hC hall (σ j)
    refine ⟨x,hx,hpx,le_trans ?_ hl⟩
    norm_num only [Nat.cast_ofNat] at hl ⊢
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC.le (sq_nonneg _)) (by positivity)

end GaussianPropeller.Reduction

end OAI


-- ---- from OAI.Probability.GaussianPropeller.Main ----
namespace OAI

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction

theorem all_partition_bound (d:ℕ) (hd:0<d) :
    ∀ k (A:Fin k→Set (Space d)), IsPartition A → value A≤9/(8*Real.pi) := by
  classical
  let : NeZero d := ⟨by omega⟩
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A hA
    by_cases hk:k≤3
    · exact partition_bound_small hk hA
    let : NeZero k := ⟨by omega⟩
    obtain ⟨B,hB⟩:=exists_minimal_optimal (d:=d) (k:=k)
    suffices hb:value B≤9/(8*Real.pi) from (hB.1.2 _ hA).trans hb
    by_contra hn
    have hC:9/(8*Real.pi)<value B := lt_of_not_ge hn
    by_cases hall:∀ j,gaussian d (B j)≠0
    · obtain ⟨D⟩:=exists_configuration (by omega) hB hC hall
      by_cases hk4:k=4
      · subst k
        exact D.impossible_four
      · exact D.impossible_five_or_more (by omega)
    · push Not at hall
      obtain ⟨i,hi⟩:=hall
      cases k with
      | zero => omega
      | succ m =>
        have hp:=remove_null_partition hB.1.1 i hi
        have hv:=ih m (by omega) (fun j=>B (i.succAbove j)) hp
        rw [remove_null_value i hi] at hv
        exact (not_le_of_gt hC) hv

end GaussianPropeller.Reduction

namespace GaussianPropeller

theorem all_partitions : AllPartitions := by
  constructor
  · intro d k hd hk A hA
    exact Reduction.all_partition_bound d hd k A hA
  · exact Reduction.propeller_attainment

end GaussianPropeller

namespace GaussianPropeller

end GaussianPropeller

end OAI

-- ---- mission target ----
open OAI OAI.GaussianPropeller
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory Set Filter
open scoped Topology BigOperators
open scoped RealInnerProductSpace Topology
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open scoped RealInnerProductSpace ENNReal

namespace OAI
namespace GaussianPropeller
theorem _root_.solution : AllPartitions := by
  first
    | exact OAI.GaussianPropeller.all_partitions
    | (apply OAI.GaussianPropeller.all_partitions <;> assumption)
    | (intros; apply OAI.GaussianPropeller.all_partitions <;> assumption)
end GaussianPropeller
end OAI
