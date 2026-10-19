-- Prove2me | solution 2 for OAI.HyperedgeComparison.column_conditional_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:58:11.95607+00:00
-- url     : https://prove2.me/submissions/6e06317b-521f-4f9f-be99-fae1e6c60d5e

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L668-L692
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.column_conditional_expectation. The node keeps its source
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
import Theorems.Thm_OAI_HyperedgeComparison_exact_cluster_weight

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

theorem clusters_singleton (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (s : V) :
    clusters H ω D {s} = cluster H ω D s := by
  ext y
  simp [clusters]

section FiniteLaw
variable [Fintype E]

/-- The first-listed-event column disintegrates over its exact root cluster. -/
theorem column_conditional_expectation [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, if firstRoot H x ω ∅ k i then g ω (cluster H ω ∅ (x k)) else 0 ∂law p) =
      column H p x k (fun U => ∫ ω, g ω U ∂law p) i := by
  classical
  have h := exact_cluster_weight H p ∅ {x k}
    (fun U => if Disjoint U (earlier x k) ∧ x i ∈ U then 1 else 0) g hg
  simp only [clusters_singleton] at h
  have heq (q : (E → Bool) → Set V → ℝ) :
      (fun ω => if firstRoot H x ω ∅ k i then q ω (cluster H ω ∅ (x k)) else 0) =
      (fun ω => (if Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧
        x i ∈ cluster H ω ∅ (x k) then (1:ℝ) else 0) * q ω (cluster H ω ∅ (x k))) := by
    funext ω
    by_cases hf : firstRoot H x ω ∅ k i
    · have hf' : Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧
          x i ∈ cluster H ω ∅ (x k) := hf
      simp [hf, hf']
    · have hf' : ¬(Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧
          x i ∈ cluster H ω ∅ (x k)) := hf
      simp [hf, hf']
  rw [← heq g, ← heq (fun _ U => ∫ ω, g ω U ∂law p)] at h
  exact h

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.column_conditional_expectation.{uE,uV} := @_root_.OAI.HyperedgeComparison.column_conditional_expectation.{uE,uV}
