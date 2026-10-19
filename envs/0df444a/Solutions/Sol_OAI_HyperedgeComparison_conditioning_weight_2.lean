-- Prove2me | solution 2 for OAI.HyperedgeComparison.conditioning_weight
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:55:25.427977+00:00
-- url     : https://prove2.me/submissions/c4ce916c-a663-4d71-b984-010e1c65178b

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L595-L622
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.conditioning_weight. The node keeps its source
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
import Theorems.Thm_OAI_HyperedgeComparison_cluster_conditioning

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

/-- Exact-cluster integration of a functional rooted outside the measured cluster. -/
theorem conditioning_weight [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S : Set V)
    (w : Set V → ℝ) (F : Set V → ℝ) (hw : ∀ U, s ∈ U → w U = 0) :
    (∫ ω, w (clusters H ω D S) * F (cluster H ω D s) ∂law p) =
      ∫ ω, w (clusters H ω D S) *
        meanAfterDelete H p s (D ∪ clusters H ω D S) F ∂law p := by
  classical
  rw [integral_eq_sum_fibers p (fun ω => clusters H ω D S),
    integral_eq_sum_fibers p (fun ω => clusters H ω D S)]
  apply Finset.sum_congr rfl
  intro U _
  have hleft : (fun ω => if clusters H ω D S = U then
      w (clusters H ω D S) * F (cluster H ω D s) else 0) =
      (fun ω => w U * (if clusters H ω D S = U then F (cluster H ω D s) else 0)) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  have hright : (fun ω => if clusters H ω D S = U then
      w (clusters H ω D S) * meanAfterDelete H p s (D ∪ clusters H ω D S) F else 0) =
      (fun ω => w U * ((if clusters H ω D S = U then (1:ℝ) else 0) *
        meanAfterDelete H p s (D ∪ U) F)) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  rw [hleft, hright, integral_const_mul, integral_const_mul, integral_mul_const]
  by_cases hs : s ∈ U
  · simp [hw U hs]
  · rw [cluster_conditioning H p s D S U F hs]
    rfl

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.conditioning_weight.{uE,uV} := @_root_.OAI.HyperedgeComparison.conditioning_weight.{uE,uV}
