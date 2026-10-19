-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.first_entry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:51:22.73672+00:00
-- url     : https://prove2.me/submissions/e742b3aa-7de8-4fc9-9ad2-41de44d8b526

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical
variable (G : LatticeGraph)
theorem cz_first_exit {V : Type*} {r : V → V → Prop} {D : Set V} {x y : V}
    (h : Relation.ReflTransGen r x y) (hx : x ∈ D) (hy : y ∉ D) :
    ∃ a ∈ D, ∃ b ∉ D, Relation.ReflTransGen (fun u v => u ∈ D ∧ v ∈ D ∧ r u v) x a ∧ r a b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hx hy
  | head hxz hzy ih =>
    rename_i x' z
    by_cases hz : z ∈ D
    · obtain ⟨a, ha, b, hb, hza, hab⟩ := ih hz
      exact ⟨a, ha, b, hb, Relation.ReflTransGen.head ⟨hx, hz, hxz⟩ hza, hab⟩
    · exact ⟨x', hx, z, hz, Relation.ReflTransGen.refl, hxz⟩

theorem cz_inc_nn {e : Bond} {x y : Vertex} (h : Incidence e x y) : NearestNeighbor x y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨e.2, Or.inl (by rw [h1, h2])⟩
  · exact ⟨e.2, Or.inr (by rw [h1, h2])⟩

theorem solution (m : Model) {C : Box} {ω : m.Config} {o z : G.Node}
    (ho : ¬C.Contains o.1) (hz : C.Contains z.1) (h : G.Conn m ω o z) :
    ∃ y w : G.Node, y.1 ∈ G.entrants m C ω o ∧ C.Contains w.1 ∧ G.Adj m ω y w := by
  have hrtg : Relation.ReflTransGen (G.Adj m ω) o z ∧ G.Open m ω o := by
    cases m
    · exact ⟨h, trivial⟩
    · exact ⟨h.2, h.1⟩
  obtain ⟨a, ha, b, hb, hoa, hab⟩ := cz_first_exit (D := {u : G.Node | ¬ C.Contains u.1}) hrtg.1 ho
    (by simpa using hz)
  refine ⟨a, b, ?_, by simpa using hb, hab⟩
  rw [mem_entrants]
  have hnn : NearestNeighbor a.1 b.1 := by
    cases m
    · obtain ⟨e, _, hinc, _⟩ := hab; exact cz_inc_nn hinc
    · obtain ⟨⟨e, _, hinc⟩, _, _⟩ := hab; exact cz_inc_nn hinc
  refine ⟨⟨ha, b.1, by simpa using hb, hnn⟩, ho, hrtg.2, ?_⟩
  refine Relation.ReflTransGen.mono (fun u v huv => ?_) _ _ hoa
  exact ⟨huv.1, huv.2.1, huv.2.2⟩

