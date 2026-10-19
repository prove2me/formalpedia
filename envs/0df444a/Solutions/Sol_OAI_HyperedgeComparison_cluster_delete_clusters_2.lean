-- Prove2me | solution 2 for OAI.HyperedgeComparison.cluster_delete_clusters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:37:57.43777+00:00
-- url     : https://prove2.me/submissions/323ed412-742d-494d-bb7e-c3e6b6992ed1

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L114-L132
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.cluster_delete_clusters. The node keeps its source
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

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

theorem adj_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Adj H ω D x y) : Adj H ω D y x := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd, hy, hx⟩

theorem connected_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Connected H ω D x y) : Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hxy ih => exact ih.head (adj_symm hxy)

theorem connected_trans {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y z : V}
    (hxy : Connected H ω D x y) (hyz : Connected H ω D y z) :
    Connected H ω D x z := hxy.trans hyz

theorem adj_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') {x y : V} (h : Adj H ω D' x y) : Adj H ω D x y := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd.mono_right hDD, hx, hy⟩

theorem cluster_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') (x : V) : cluster H ω D' x ⊆ cluster H ω D x :=
  Relation.ReflTransGen.mono (fun _ _ => adj_mono_delete hDD) x

theorem clusters_closed {H : Hypergraph V E} {ω : E → Bool} {D S : Set V} {x y : V}
    (hx : x ∈ clusters H ω D S) (hxy : Adj H ω D x y) : y ∈ clusters H ω D S := by
  obtain ⟨s, hs, hx⟩ := hx
  exact ⟨s, hs, hx.tail hxy⟩

/-- Deleting a union of clusters does not change any of the other clusters.
This is deterministic, before any product-law conditioning. -/
theorem cluster_delete_clusters {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {x : V} (hx : x ∉ clusters H ω D S) :
    cluster H ω (D ∪ clusters H ω D S) x = cluster H ω D x := by
  apply Set.Subset.antisymm (cluster_mono_delete Set.subset_union_left x)
  intro y hy
  have hall : ∀ z ∈ cluster H ω D x, z ∉ clusters H ω D S := by
    rintro z hz ⟨s, hs, hsz⟩
    exact hx ⟨s, hs, connected_trans hsz (connected_symm hz)⟩
  induction hy with
  | refl => exact .refl
  | @tail z y hxz hzy ih =>
    apply ih.tail
    obtain ⟨e, he, hd, hz, hy⟩ := hzy
    refine ⟨e, he, Disjoint.union_right hd ?_, hz, hy⟩
    apply Set.disjoint_left.mpr
    intro a ha hbad
    exact hall z hxz (clusters_closed hbad ⟨e, he, hd, ha, hz⟩)

section FiniteLaw
variable [Fintype E]

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.cluster_delete_clusters.{uE,uV} := @_root_.OAI.HyperedgeComparison.cluster_delete_clusters.{uE,uV}
