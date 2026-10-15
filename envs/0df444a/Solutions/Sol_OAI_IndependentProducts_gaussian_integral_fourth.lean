-- Prove2me | solution 1 for OAI.IndependentProducts.gaussian_integral_fourth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:05:27.769503+00:00
-- url     : https://prove2.me/submissions/3ecc8ca3-21cf-43f8-86b4-8d59573f3a0c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean:L59-L96
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.gaussian_integral_fourth. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds

-- ---- from OAI.Analysis.ProductSpaces.ScalarBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

lemma gaussian_integral_fourth : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  have hmgf : mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t => Real.exp (t ^ 2 / 2) := by
    simpa using mgf_fun_id_gaussianReal (μ := 0) (v := 1)
  have d1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [_root_.deriv_exp (by fun_prop)]
    rw [deriv_div_const, deriv_pow_field]
    norm_num
    ring
  have d2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    change _ + t * (deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) t) = _
    rw [d1]
    simp only [deriv_id'']
    ring
  have d3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    change _ + (1 + t ^ 2) * (deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) t) = _
    rw [d1]
    rw [deriv_const_add, deriv_pow_field]
    norm_num
    ring
  have d4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) 0 = 3 := by
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    have hp : deriv (fun t : ℝ => 3 * t + t ^ 3) 0 = 3 := by
      rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const_mul 3 (by fun_prop), deriv_pow_field]
      norm_num
    rw [hp]
    norm_num
  have hiff : (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by simp
  have he := iteratedDeriv_mgf_zero hiff 4
  rw [hmgf, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    d1, d2, d3, d4] at he
  exact he.symm

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

variable [IsProbabilityMeasure μ]

end SecondMoment
end IndependentProducts

namespace IndependentProducts

section GaussianSum
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

variable [Fintype ι]

end GaussianSum
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι

theorem solution : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  first
    | exact OAI.IndependentProducts.gaussian_integral_fourth
    | (apply OAI.IndependentProducts.gaussian_integral_fourth <;> assumption)
    | (intros; apply OAI.IndependentProducts.gaussian_integral_fourth <;> assumption)
