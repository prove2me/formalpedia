-- Prove2me | solution 1 for OAI.HyperedgeComparison.clusters_eq_of_agree_incident
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:32:08.565398+00:00
-- url     : https://prove2.me/submissions/e2f33ca8-3bf7-4178-aba7-15a70eea3ff3

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

theorem solution {H : Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V}
    (hagree : ∀ e, ¬ Disjoint (H e) (clusters H ω D S) → ω' e = ω e) :
    clusters H ω' D S = clusters H ω D S := by
  have key : ∀ s ∈ S, ∀ y, (Connected H ω' D s y ↔ Connected H ω D s y) := by
    intro s hs y
    constructor
    · intro h
      induction h with
      | refl => exact .refl
      | @tail z w hsz hab ih =>
        obtain ⟨e, h1, h2, h3, h4⟩ := hab
        have hzC : z ∈ clusters H ω D S := ⟨s, hs, ih⟩
        have : ω' e = ω e := hagree e (Set.not_disjoint_iff.mpr ⟨z, h3, hzC⟩)
        exact Relation.ReflTransGen.tail ih ⟨e, this ▸ h1, h2, h3, h4⟩
    · intro h
      induction h with
      | refl => exact .refl
      | @tail z w hsz hab ih =>
        obtain ⟨e, h1, h2, h3, h4⟩ := hab
        have hzC : z ∈ clusters H ω D S := ⟨s, hs, hsz⟩
        have : ω' e = ω e := hagree e (Set.not_disjoint_iff.mpr ⟨z, h3, hzC⟩)
        exact Relation.ReflTransGen.tail ih ⟨e, this.trans h1, h2, h3, h4⟩
  ext y
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (key s hs y).mp h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (key s hs y).mpr h⟩

