-- Prove2me | solution 2 for OAI.GaussianPropeller.sum_centroid_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:33:48.422158+00:00
-- url     : https://prove2.me/submissions/c75e4d65-7d71-4e7e-ac4e-5897ee035c48

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Moments.lean:L47-L59
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.sum_centroid_eq_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments

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

theorem sum_centroid_eq_zero {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : ∑ i, centroid (A i) = 0 := by
  have hi (i : Fin k) : Integrable ((A i).indicator (fun x => x)) (gaussian d) :=
    (integrable_id_gaussian d).indicator (hA.1 i)
  calc
    ∑ i, centroid (A i) = ∑ i, ∫ x, (A i).indicator (fun x => x) x ∂gaussian d := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_indicator (hA.1 i)).symm
    _ = ∫ x, ∑ i, (A i).indicator (fun x => x) x ∂gaussian d :=
      (integral_finsetSum _ (fun i _ => hi i)).symm
    _ = ∫ x, x ∂gaussian d := integral_congr_ae (sum_indicator_eq hA (fun x => x))
    _ = 0 := integral_id_stdGaussian

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.sum_centroid_eq_zero := @_root_.OAI.GaussianPropeller.sum_centroid_eq_zero
