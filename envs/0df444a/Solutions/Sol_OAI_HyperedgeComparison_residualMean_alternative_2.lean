-- Prove2me | solution 2 for OAI.HyperedgeComparison.residualMean_alternative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:56:53.027348+00:00
-- url     : https://prove2.me/submissions/1a9c1278-8e4a-4139-9746-507d3145fe98

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L624-L651
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.residualMean_alternative. The node keeps its source
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
import Theorems.Thm_OAI_HyperedgeComparison_conditioning_weight

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

/-- For residuals, after conditioning on W the second sample may instead be
read in the original configuration on the graph with U deleted. -/
theorem residualMean_alternative [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S U : Set V) (F : Set V → ℝ) :
    residualMean H p s S U F =
      ∫ ω, if s ∈ clusters H ω U S then 0 else
        meanAfterDelete H p s (clusters H ω U S) F - F (cluster H ω U s) ∂law p := by
  classical
  have hc := conditioning_weight H p s U S
    (fun W => if s ∈ W then 0 else 1) F (by intro W h; simp [h])
  have heq₁ : (fun ω => if s ∈ clusters H ω U S then (0:ℝ) else
      meanAfterDelete H p s (clusters H ω U S) F - F (cluster H ω U s)) =
      (fun ω => (if s ∈ clusters H ω U S then 0 else meanAfterDelete H p s
        (clusters H ω U S) F) - (if s ∈ clusters H ω U S then 0 else 1) *
          F (cluster H ω U s)) := by
    funext ω
    split_ifs <;> simp
  have heq₂ : (fun ω => if s ∈ clusters H ω U S then (0:ℝ) else
      meanAfterDelete H p s (clusters H ω U S) F -
        meanAfterDelete H p s (clusters H ω U S ∪ U) F) =
      (fun ω => (if s ∈ clusters H ω U S then 0 else meanAfterDelete H p s
        (clusters H ω U S) F) - (if s ∈ clusters H ω U S then 0 else 1) *
          meanAfterDelete H p s (U ∪ clusters H ω U S) F) := by
    funext ω
    split_ifs <;> simp [Set.union_comm]
  unfold residualMean
  rw [heq₁, heq₂, integral_sub (Integrable.of_finite) (Integrable.of_finite),
    integral_sub (Integrable.of_finite) (Integrable.of_finite), hc]

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.residualMean_alternative.{uE,uV} := @_root_.OAI.HyperedgeComparison.residualMean_alternative.{uE,uV}
