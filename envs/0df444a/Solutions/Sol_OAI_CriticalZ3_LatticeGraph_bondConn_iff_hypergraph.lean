-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.bondConn_iff_hypergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:36:07.802929+00:00
-- url     : https://prove2.me/submissions/936d88ba-097d-430b-8da2-f2f6d8e2415a

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical MeasureTheory ProbabilityTheory
variable (G : LatticeGraph)


theorem solution (ω : BondConfig) (x y : G.Node) :
    G.BondConn ω x y ↔ HyperedgeComparison.Connected G.hypergraph
      (fun e => ω e.1) ∅ x y := by
  unfold LatticeGraph.BondConn HyperedgeComparison.Connected
  constructor
  · intro h
    refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _ h
    obtain ⟨e, he, hinc, hω⟩ := hab
    refine ⟨⟨e, he⟩, hω, Set.disjoint_empty _, ?_, ?_⟩ <;>
      rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> first | exact Or.inl h1 | exact Or.inr h1 | exact Or.inl h2 | exact Or.inr h2
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih =>
      obtain ⟨⟨e, he⟩, hω, -, ha, hb⟩ := hab
      by_cases hab' : a = b
      · subst hab'; exact ih
      · refine ih.tail ⟨e, he, ?_, hω⟩
        change a.1 = e.1 ∨ a.1 = step e.1 e.2 at ha
        change b.1 = e.1 ∨ b.1 = step e.1 e.2 at hb
        have hne : a.1 ≠ b.1 := fun h => hab' (Subtype.ext h)
        unfold Incidence
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact absurd (ha.trans hb.symm) hne
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr ⟨hb, ha⟩
        · exact absurd (ha.trans hb.symm) hne

