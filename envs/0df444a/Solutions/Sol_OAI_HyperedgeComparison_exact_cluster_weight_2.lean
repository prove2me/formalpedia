-- Prove2me | solution 2 for OAI.HyperedgeComparison.exact_cluster_weight
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:53:47.950146+00:00
-- url     : https://prove2.me/submissions/ece7022c-3d9b-4446-b375-455d0eef57bf

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L568-L593
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.exact_cluster_weight. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Theorems.Thm_OAI_HyperedgeComparison_exact_cluster_independent

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

section FiniteLaw
variable [Fintype E]

/-- Integrated exact-cluster independence, with no positivity restriction on
an exact cluster event (zero probability events also satisfy the identity). -/
theorem exact_cluster_integral (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    (∫ ω, (if clusters H ω D S = W then (1 : ℝ) else 0) * g ω ∂law p) =
      (∫ ω, if clusters H ω D S = W then (1 : ℝ) else 0 ∂law p) *
        ∫ ω, g ω ∂law p := by
  classical
  exact (exact_cluster_independent H p D S W g hg).integral_fun_mul_eq_mul_integral
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- Partition a finite expectation by exact values, without conditional-probability
notation and without requiring positive individual atom masses. -/
theorem integral_eq_sum_fibers {I : Type uI} [Fintype I] [DecidableEq I]
    (p : E → Set.Icc (0 : ℝ) 1) (X : (E → Bool) → I) (f : (E → Bool) → ℝ) :
    (∫ ω, f ω ∂law p) = ∑ i, ∫ ω, if X ω = i then f ω else 0 ∂law p := by
  classical
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  congr 1
  funext ω
  simp

/-- Multiply the exact-cluster identity by an arbitrary function of the cluster.
No positive-probability conditioning is needed. -/
theorem exact_cluster_weight [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S : Set V) (f : Set V → ℝ)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, f (clusters H ω D S) * g ω (clusters H ω D S) ∂law p) =
      ∫ ω, f (clusters H ω D S) * (∫ ω', g ω' (clusters H ω D S) ∂law p) ∂law p := by
  classical
  rw [integral_eq_sum_fibers p (fun ω => clusters H ω D S),
    integral_eq_sum_fibers p (fun ω => clusters H ω D S)]
  apply Finset.sum_congr rfl
  intro U _
  have hleft : (fun ω => if clusters H ω D S = U then
      f (clusters H ω D S) * g ω (clusters H ω D S) else 0) =
      (fun ω => f U * ((if clusters H ω D S = U then (1:ℝ) else 0) * g ω U)) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  have hright : (fun ω => if clusters H ω D S = U then
      f (clusters H ω D S) * (∫ ω', g ω' (clusters H ω D S) ∂law p) else 0) =
      (fun ω => f U * ((if clusters H ω D S = U then (1:ℝ) else 0) *
        (∫ ω', g ω' U ∂law p))) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  rw [hleft, hright, integral_const_mul, integral_const_mul, integral_mul_const,
    exact_cluster_integral H p D S U (fun ω => g ω U) (hg U)]

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

end OAI

-- ---- platform node ----
open OAI OAI.HyperedgeComparison
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.exact_cluster_weight.{uE,uV} := @_root_.OAI.HyperedgeComparison.exact_cluster_weight.{uE,uV}
