-- Prove2me | solution 2 for OAI.CriticalZ3.LatticeGraph.first_entry
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:26:47.553976+00:00
-- url     : https://prove2.me/submissions/6aaa2c26-836a-4dff-b029-faabb09559db

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/EntryLayers.lean:L122-L140
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.first_entry. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers

-- ---- from OAI.Probability.CriticalZ3.LatticeGraph ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open Classical MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory

theorem incidence_neighbor {e : Bond} {x y : Vertex} (h : Incidence e x y) :
    NearestNeighbor x y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨e.2,Or.inl rfl⟩
  · exact ⟨e.2,Or.inr rfl⟩

namespace LatticeGraph
variable (G : LatticeGraph)

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.LatticePaths ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

namespace Model
end Model

namespace Box
end Box

namespace LatticeGraph
variable (G : LatticeGraph)
theorem conn_iff (m : Model) (ω : m.Config) (x y : G.Node) :
    G.Conn m ω x y ↔ G.Open m ω x ∧ Relation.ReflTransGen (G.Adj m ω) x y := by
  cases m
  · exact ⟨fun h => ⟨trivial,h⟩,fun h => h.2⟩
  · rfl

theorem adj_neighbor (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    NearestNeighbor x.1 y.1 := by
  cases m
  · obtain ⟨e,_,he,_⟩ := h; exact incidence_neighbor he
  · obtain ⟨⟨e,_,he⟩,_⟩ := h; exact incidence_neighbor he

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.EntryLayers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

namespace Box

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

theorem first_entry (m : Model) {C : Box} {ω : m.Config} {o z : G.Node}
    (ho : ¬C.Contains o.1) (hz : C.Contains z.1) (h : G.Conn m ω o z) :
    ∃ y w : G.Node, y.1 ∈ G.entrants m C ω o ∧ C.Contains w.1 ∧ G.Adj m ω y w := by
  have hp := ((G.conn_iff m ω o z).mp h).2
  have hop := ((G.conn_iff m ω o z).mp h).1
  have hh : ∀ {x : G.Node}, Relation.ReflTransGen (G.Adj m ω) o x →
      (¬C.Contains x.1 ∧ Relation.ReflTransGen (G.OutsideAdj m C ω) o x) ∨
      ∃ y w : G.Node, y.1 ∈ G.entrants m C ω o ∧ C.Contains w.1 ∧ G.Adj m ω y w := by
    intro x hx
    induction hx with
    | refl => exact Or.inl ⟨ho,.refl⟩
    | @tail a b _ hab ih =>
      rcases ih with ⟨ha,hi⟩ | he
      · by_cases hb : C.Contains b.1
        · exact Or.inr ⟨a,b,(G.mem_entrants m C ω o a).mpr
            ⟨⟨ha,b.1,hb,G.adj_neighbor m hab⟩,ho,hop,hi⟩,hb,hab⟩
        · exact Or.inl ⟨hb,hi.tail ⟨ha,hb,hab⟩⟩
      · exact Or.inr he
  exact (hh hp).resolve_left (fun h => h.1 hz)

end LatticeGraph
end CriticalZ3

namespace CriticalZ3.LatticeGraph
open Classical
variable (G : LatticeGraph)

end CriticalZ3.LatticeGraph

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.first_entry := @_root_.OAI.CriticalZ3.LatticeGraph.first_entry
