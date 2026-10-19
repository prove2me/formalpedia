-- Prove2me | solution 2 for OAI.HyperedgeComparison.exact_cluster_independent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:47:22.415996+00:00
-- url     : https://prove2.me/submissions/91ce331c-e328-4b24-963d-b1df878010d4

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L369-L398
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.exact_cluster_independent. The node keeps its source
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
import Theorems.Thm_OAI_HyperedgeComparison_clusters_eq_of_agree_incident
import Theorems.Thm_OAI_HyperedgeComparison_independent_of_disjoint_bits

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

/-- The exact-cluster indicator sees no bit on a hyperedge disjoint from W,
including when the cluster was sampled after an earlier deletion D. -/
theorem exact_cluster_independent (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    IndepFun (fun ω => if clusters H ω D S = W then (1 : ℝ) else 0) g (law p) := by
  classical
  apply independent_of_disjoint_bits p (Finset.univ.filter (fun e => ¬ Disjoint (H e) W))
  · intro ω ω' hagree
    have heq : clusters H ω' D S = W ↔ clusters H ω D S = W := by
      constructor
      · intro h
        have hh : clusters H ω D S = clusters H ω' D S := by
          apply clusters_eq_of_agree_incident
          intro e he
          rw [h] at he
          exact (hagree e (by simp [he])).symm
        exact hh.trans h
      · intro h
        have hh : clusters H ω' D S = clusters H ω D S := by
          apply clusters_eq_of_agree_incident
          intro e he
          rw [h] at he
          exact hagree e (by simp [he])
        exact hh.trans h
    simp only [heq]
  · intro ω ω' hagree
    apply hg ω ω'
    intro e he
    exact hagree e (by simp [he])

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.exact_cluster_independent.{uE,uV} := @_root_.OAI.HyperedgeComparison.exact_cluster_independent.{uE,uV}
