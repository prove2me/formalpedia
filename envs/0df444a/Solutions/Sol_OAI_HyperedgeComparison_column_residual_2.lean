-- Prove2me | solution 2 for OAI.HyperedgeComparison.column_residual
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:59:55.641232+00:00
-- url     : https://prove2.me/submissions/f009c502-ca44-484c-aadc-48e9b430f962

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L720-L754
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.column_residual. The node keeps its source
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
import Theorems.Thm_OAI_HyperedgeComparison_column_conditional_expectation
import Theorems.Thm_OAI_HyperedgeComparison_residualMean_alternative

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

theorem adj_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') {x y : V} (h : Adj H ω D' x y) : Adj H ω D x y := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd.mono_right hDD, hx, hy⟩

theorem cluster_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') (x : V) : cluster H ω D' x ⊆ cluster H ω D x :=
  Relation.ReflTransGen.mono (fun _ _ => adj_mono_delete hDD) x

theorem clusters_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' S : Set V}
    (hDD : D ⊆ D') : clusters H ω D' S ⊆ clusters H ω D S := by
  rintro y ⟨x, hx, hy⟩
  exact ⟨x, hx, cluster_mono_delete hDD x hy⟩

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

theorem clusters_eq_of_agree_disjoint {H : Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V} (hagree : ∀ e, Disjoint (H e) D → ω' e = ω e) :
    clusters H ω' D S = clusters H ω D S := by
  unfold clusters
  simp only [cluster_eq_of_agree_disjoint hagree]

theorem clusters_singleton (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (s : V) :
    clusters H ω D {s} = cluster H ω D s := by
  ext y
  simp [clusters]

/-- Deleting a cluster does not change the union of any disjoint clusters. -/
theorem clusters_delete_cluster {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {s : V} (h : Disjoint (cluster H ω D s) S) :
    clusters H ω (D ∪ cluster H ω D s) S = clusters H ω D S := by
  ext y
  constructor
  · exact fun hy => clusters_mono_delete Set.subset_union_left hy
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, hx, ?_⟩
    have heq := cluster_delete_clusters (H := H) (ω := ω) (D := D) (S := {s})
      (x := x) (by simpa only [clusters_singleton] using (fun hxs => Set.disjoint_left.mp h hxs hx))
    rw [clusters_singleton] at heq
    rwa [heq]

section FiniteLaw
variable [Fintype E]

/-- An earlier list segment is included in every later segment. -/
theorem earlier_mono {n : ℕ} (x : Fin n → V) {k j : Fin n} (hkj : k ≤ j) :
    earlier x k ⊆ earlier x j := by
  rintro y ⟨l, hl, hly⟩
  exact ⟨l, lt_of_lt_of_le hl hkj, hly⟩

/-- The residual term after conditioning on C(x_j), retaining the original
configuration only on hyperedges disjoint from that cluster. -/
theorem column_residual [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k j i : Fin n)
    (hkj : k < j) (F : Set V → ℝ) :
    column H p x j (residualMean H p (x k) (earlier x k) · F) i =
      ∫ ω, if firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k) then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F -
          F (cluster H ω ∅ (x k)) else 0 ∂law p := by
  classical
  have hfun : (fun U => residualMean H p (x k) (earlier x k) U F) =
      (fun U => ∫ ω, if x k ∈ clusters H ω U (earlier x k) then 0 else
        meanAfterDelete H p (x k) (clusters H ω U (earlier x k)) F -
          F (cluster H ω U (x k)) ∂law p) := by
    funext U
    exact residualMean_alternative H p (x k) (earlier x k) U F
  rw [hfun]
  rw [← column_conditional_expectation H p x j i _ (by
    intro U ω ω' hagree
    rw [clusters_eq_of_agree_disjoint hagree, cluster_eq_of_agree_disjoint hagree])]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ j i
  · have hdis : Disjoint (cluster H ω ∅ (x j)) (earlier x k) :=
      hf.1.mono_right (earlier_mono x hkj.le)
    have hs : x k ∉ cluster H ω ∅ (x j) := fun hs =>
      Set.disjoint_left.mp hf.1 hs ⟨k, hkj, rfl⟩
    have hW := clusters_delete_cluster hdis
    have hC := cluster_delete_clusters (H := H) (ω := ω) (D := ∅) (S := {x j})
      (x := x k) (by simpa only [clusters_singleton] using hs)
    simp only [Set.empty_union, clusters_singleton] at hW hC
    simp only [hf, ite_true, hW, hC, true_and]
    split_ifs <;> simp_all
  · simp [hf]

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.column_residual.{uE,uV} := @_root_.OAI.HyperedgeComparison.column_residual.{uE,uV}
