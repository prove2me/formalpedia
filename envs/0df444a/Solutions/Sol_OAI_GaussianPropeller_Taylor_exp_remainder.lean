-- Prove2me | solution 1 for OAI.GaussianPropeller.Taylor.exp_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:30:09.334988+00:00
-- url     : https://prove2.me/submissions/7f9302a5-dd58-438c-8312-ed1ce6edcb8c

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Taylor.lean:L41-L57
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Taylor.exp_remainder. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor

-- ---- from OAI.Probability.GaussianPropeller.Taylor ----
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

namespace GaussianPropeller.Taylor
lemma exp_remainder {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∃ c : ℝ, Real.exp (-x)-E n x =
      (-1:ℝ)^(n+1)*Real.exp (-c)*x^(n+1)/(Nat.factorial (n+1)) := by
  obtain ⟨c,hc,h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := fun t : ℝ => Real.exp ((-1)*t)) (x₀ := 0) (x := x) (n := n) hx.ne
    (by fun_prop)
  refine ⟨c, ?_⟩
  have he : taylorWithinEval (fun t : ℝ => Real.exp ((-1)*t)) n (uIcc 0 x) 0 x = E n x := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.ne)
      (by fun_prop) (by simp), iteratedDeriv_exp_const_mul]
    simp only [mul_zero, Real.exp_zero, mul_one, sub_zero, smul_eq_mul]
    ring
  rw [he, iteratedDeriv_exp_const_mul] at h
  simpa only [neg_one_mul, sub_zero, mul_assoc] using h

end GaussianPropeller.Taylor

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Taylor
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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Taylor.exp_remainder := @_root_.OAI.GaussianPropeller.Taylor.exp_remainder
