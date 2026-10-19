-- Prove2me | solution 2 for OAI.GaussianPropeller.Reduction.pairing_le_width
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:38:08.507726+00:00
-- url     : https://prove2.me/submissions/24c334fb-b066-4f20-9d06-57ab612994df

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Dual.lean:L167-L181
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.pairing_le_width. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

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

theorem pairing_le_width {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) : ⟪v, moments A⟫ ≤ width v := by
  classical
  rw [pairing_integral hA]
  have hi : Integrable (fun x => ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x)
      (gaussian d) := integrable_finsetSum _ (fun i _ =>
        ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1 i))
  apply integral_mono_ae hi (integrable_scoreMax v)
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, huniq⟩ := hx
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using le_scoreMax v.ofLp i x
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

end Reduction

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.pairing_le_width := @_root_.OAI.GaussianPropeller.Reduction.pairing_le_width
