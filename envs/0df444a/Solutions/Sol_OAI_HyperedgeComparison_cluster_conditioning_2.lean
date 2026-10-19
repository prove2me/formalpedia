-- Prove2me | solution 2 for OAI.HyperedgeComparison.cluster_conditioning
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:51:16.987535+00:00
-- url     : https://prove2.me/submissions/6e48d03d-2ee4-49f6-be12-55f21b9a6368

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L544-L566
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.cluster_conditioning. The node keeps its source
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
import Theorems.Thm_OAI_HyperedgeComparison_cluster_delete_clusters
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

/-- Bits on deleted hyperedges are irrelevant to the surviving clusters. -/
theorem cluster_eq_of_agree_disjoint {H : Hypergraph V E} {ω ω' : E → Bool}
    {D : Set V} (hagree : ∀ e, Disjoint (H e) D → ω' e = ω e) (s : V) :
    cluster H ω' D s = cluster H ω D s := by
  have hrel : Adj H ω' D = Adj H ω D := by
    funext x y
    apply propext
    constructor <;> rintro ⟨e, he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd) ▸ he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd).trans he, hd, hx, hy⟩
  unfold cluster Connected
  rw [hrel]

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

/-- The exact-cluster conditional expectation used in the column partition. -/
theorem cluster_conditioning (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S W : Set V) (F : Set V → ℝ)
    (hs : s ∉ W) :
    (∫ ω, if clusters H ω D S = W then F (cluster H ω D s) else 0 ∂law p) =
      clusterMass H p D S W * meanAfterDelete H p s (D ∪ W) F := by
  classical
  have hind := exact_cluster_integral H p D S W
    (fun ω => F (cluster H ω (D ∪ W) s)) (by
      intro ω ω' hagree
      rw [cluster_eq_of_agree_disjoint
        (fun e he => hagree e (he.mono_right Set.subset_union_right)) s])
  unfold clusterMass meanAfterDelete
  rw [← hind]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases h : clusters H ω D S = W
  · have hcs : cluster H ω (D ∪ W) s = cluster H ω D s := by
      rw [← h]
      exact cluster_delete_clusters (by rwa [h])
    simp [h, hcs]
  · simp [h]

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.cluster_conditioning.{uE,uV} := @_root_.OAI.HyperedgeComparison.cluster_conditioning.{uE,uV}
