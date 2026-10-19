-- Prove2me | solution 2 for OAI.GaussianPropeller.Reduction.width_moments_of_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:39:33.685497+00:00
-- url     : https://prove2.me/submissions/eb360e94-f2fe-47bc-b0f8-22431d5358ff

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Dual.lean:L391-L404
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.width_moments_of_optimal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Theorems.Thm_OAI_GaussianPropeller_Reduction_exists_unique_scoreCell
import Theorems.Thm_OAI_GaussianPropeller_Reduction_pairing_le_width

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

theorem width_moments_of_optimal {A : Fin k → Set (Space d)} (hA : Optimal A) :
    width (moments A) = value A := by
  have hnorm : ‖moments (scoreCell (moments A).ofLp)‖ ≤ ‖moments A‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_moments_sq, norm_moments_sq]
    exact hA.2 _ (scoreCell_partition _)
  apply le_antisymm
  · rw [← pairing_scoreCell, ← norm_moments_sq]
    calc
      ⟪moments A, moments (scoreCell (moments A).ofLp)⟫ ≤
          ‖moments A‖ * ‖moments (scoreCell (moments A).ofLp)‖ := real_inner_le_norm _ _
      _ ≤ ‖moments A‖ * ‖moments A‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = ‖moments A‖ ^ 2 := (sq _).symm
  · simpa only [real_inner_self_eq_norm_sq, norm_moments_sq] using pairing_le_width hA.1 (moments A)

end Reduction

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.width_moments_of_optimal := @_root_.OAI.GaussianPropeller.Reduction.width_moments_of_optimal
