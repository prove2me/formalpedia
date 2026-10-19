-- Prove2me | solution 2 for OAI.GaussianPropeller.Reduction.optimal_loss_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:48:07.957344+00:00
-- url     : https://prove2.me/submissions/ea59e69d-963a-4d5c-a5bf-5d13b37455a6

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Deletion.lean:L180-L202
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.optimal_loss_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Theorems.Thm_OAI_GaussianPropeller_Reduction_exists_unique_scoreCell
import Theorems.Thm_OAI_GaussianPropeller_Reduction_recentered_norm_sq
import Theorems.Thm_OAI_GaussianPropeller_Reduction_scoreMax_recentered
import Theorems.Thm_OAI_GaussianPropeller_Reduction_width_moments_of_optimal
import Theorems.Thm_OAI_GaussianPropeller_sum_centroid_eq_zero

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

end Reduction

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Deletion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open scoped RealInnerProductSpace

namespace GaussianPropeller.Reduction

variable {d k : ℕ} [NeZero k]

theorem optimal_width_le {A : Fin k → Set (Space d)} (hA : Optimal A)
    (v : Tuple d k) : width v ≤ Real.sqrt (value A) * ‖v‖ := by
  have hn : ‖moments (scoreCell v.ofLp)‖ ≤ Real.sqrt (value A) := by
    apply (Real.le_sqrt (norm_nonneg _) (value_nonneg A)).mpr
    rw [norm_moments_sq]
    exact hA.2 _ (scoreCell_partition _)
  rw [← pairing_scoreCell]
  calc
    ⟪v, moments (scoreCell v.ofLp)⟫ ≤ ‖v‖ * ‖moments (scoreCell v.ofLp)‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * Real.sqrt (value A) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := mul_comm _ _

lemma omittedMax_integrable (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    Integrable (omittedMax hk z i) (gaussian d) := by
  have heq : omittedMax hk z i = fun x => scoreMax (recentered z i).ofLp x -
      ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
    funext x
    rw [scoreMax_recentered hk z hz i x]
    ring
  rw [heq]
  exact (integrable_scoreMax _).sub
    (Integrable.const_inner _ (integrable_id_gaussian d))

lemma integral_omittedMax (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ∫ x, omittedMax hk z i x ∂gaussian d = width (recentered z i) := by
  have heq : scoreMax (recentered z i).ofLp = fun x => omittedMax hk z i x +
      ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := funext (scoreMax_recentered hk z hz i)
  rw [width, heq]
  change _ = ∫ x, omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ ∂gaussian d
  have hi : Integrable (fun x : Space d => ⟪((k:ℝ)-1)⁻¹ • z i,x⟫) (gaussian d) :=
    Integrable.const_inner _ (integrable_id_gaussian d)
  rw [integral_add (omittedMax_integrable hk z hz i) hi]
  have hz0 : (∫ x : Space d, ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ ∂gaussian d) = 0 := by
    rw [integral_inner (integrable_id_gaussian d)]
    simp only [gaussian, integral_id_stdGaussian, inner_zero_right]
  rw [hz0, add_zero]

lemma scoreMax_eq_max_omitted (hk : 2 ≤ k) (z : Fin k → Space d)
    (i : Fin k) (x : Space d) : scoreMax z x = max ⟪z i,x⟫ (omittedMax hk z i x) := by
  classical
  apply le_antisymm
  · apply (scoreMax_le_iff _ _ _).mpr
    intro j
    by_cases hji : j = i
    · subst j
      exact le_max_left _ _
    · exact (Finset.le_sup' (fun j => ⟪z j,x⟫)
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)).trans (le_max_right _ _)
  · apply max_le
    · exact le_scoreMax z i x
    · exact Finset.sup'_le _ _ (fun j _ => le_scoreMax z j x)

lemma positive_gap_eq (hk : 2 ≤ k) (z : Fin k → Space d)
    (i : Fin k) (x : Space d) :
    max (⟪z i,x⟫ - omittedMax hk z i x) 0 = scoreMax z x - omittedMax hk z i x := by
  rw [scoreMax_eq_max_omitted hk z i x]
  simpa only [sub_self] using max_sub_sub_right ⟪z i,x⟫ (omittedMax hk z i x) (omittedMax hk z i x)

theorem optimal_loss_lower (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : Optimal A) (i : Fin k) :
    value A - Real.sqrt (value A) *
      Real.sqrt (value A - ((k:ℝ)/((k:ℝ)-1)) * ‖centroid (A i)‖^2) ≤
    ∫ x, max (⟪centroid (A i),x⟫ -
      omittedMax hk (fun j => centroid (A j)) i x) 0 ∂gaussian d := by
  let z : Fin k → Space d := fun j => centroid (A j)
  have hz : ∑ j, z j = 0 := sum_centroid_eq_zero hA.1
  have hn : ‖recentered z i‖ =
      Real.sqrt (value A - ((k:ℝ)/((k:ℝ)-1)) * ‖centroid (A i)‖^2) := by
    rw [← show ‖recentered z i‖^2 = value A - ((k:ℝ)/((k:ℝ)-1)) *
      ‖centroid (A i)‖^2 from recentered_norm_sq hk z hz i, Real.sqrt_sq (norm_nonneg _)]
  have heq : (fun x => max (⟪centroid (A i),x⟫ - omittedMax hk z i x) 0) =
      fun x => scoreMax z x - omittedMax hk z i x := funext (positive_gap_eq hk z i)
  change _ ≤ ∫ x, max (⟪centroid (A i),x⟫ - omittedMax hk z i x) 0 ∂gaussian d
  rw [heq]
  have hiz : Integrable (scoreMax z) (gaussian d) := integrable_scoreMax (WithLp.toLp 2 z)
  rw [integral_sub hiz (omittedMax_integrable hk z hz i), integral_omittedMax hk z hz i]
  change _ ≤ width (moments A) - width (recentered z i)
  rw [width_moments_of_optimal hA]
  have hb := optimal_width_le hA (recentered z i)
  rw [hn] at hb
  linarith

end GaussianPropeller.Reduction

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.optimal_loss_lower := @_root_.OAI.GaussianPropeller.Reduction.optimal_loss_lower
