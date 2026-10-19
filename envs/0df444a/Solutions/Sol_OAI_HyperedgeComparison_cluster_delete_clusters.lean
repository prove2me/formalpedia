-- Prove2me | solution 1 for OAI.HyperedgeComparison.cluster_delete_clusters
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:31:58.391432+00:00
-- url     : https://prove2.me/submissions/5db55971-9a93-4f61-b088-66cc6b75d040

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

open OAI OAI.HyperedgeComparison
universe uE uI uV
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
variable {V : Type uV} {E : Type uE}
theorem hc_adj_symm {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Adj H ω D x y) :
    OAI.HyperedgeComparison.Adj H ω D y x := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  exact ⟨e, h1, h2, h4, h3⟩

theorem hc_conn_symm {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Connected H ω D x y) :
    OAI.HyperedgeComparison.Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (hc_adj_symm hab) ih

theorem hc_conn_trans {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y z : V} (h : OAI.HyperedgeComparison.Connected H ω D x y)
    (h' : OAI.HyperedgeComparison.Connected H ω D y z) :
    OAI.HyperedgeComparison.Connected H ω D x z :=
  Relation.ReflTransGen.trans h h'

theorem solution {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {x : V} (hx : x ∉ clusters H ω D S) :
    cluster H ω (D ∪ clusters H ω D S) x = cluster H ω D x := by
  -- key: any vertex connected (avoiding D) to x is not in the clusters, and its hyperedges avoid them
  have hnot : ∀ y, Connected H ω D x y → ∀ s ∈ S, ¬ Connected H ω D s y := by
    intro y hy s hs hsy
    exact hx ⟨s, hs, hc_conn_trans hsy (hc_conn_symm hy)⟩
  ext y
  constructor
  · intro hy
    show Connected H ω D x y
    induction hy with
    | refl => exact .refl
    | tail _ hab ih =>
      obtain ⟨e, h1, h2, h3, h4⟩ := hab
      exact Relation.ReflTransGen.tail ih ⟨e, h1, h2.mono_right Set.subset_union_left, h3, h4⟩
  · intro hy
    show Connected H ω (D ∪ clusters H ω D S) x y
    change Connected H ω D x y at hy
    induction hy with
    | refl => exact .refl
    | @tail z w hxz hab ih =>
      obtain ⟨e, h1, h2, h3, h4⟩ := hab
      refine Relation.ReflTransGen.tail ih ⟨e, h1, ?_, h3, h4⟩
      rw [Set.disjoint_union_right]
      refine ⟨h2, Set.disjoint_left.mpr ?_⟩
      rintro u hu ⟨s, hs, hsu⟩
      exact hnot z hxz s hs (hc_conn_trans hsu (Relation.ReflTransGen.single ⟨e, h1, h2, hu, h3⟩))

