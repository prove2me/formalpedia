-- Prove2me | solution 2 for OAI.CriticalZ3.LatticeGraph.lift_path
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:25:27.456099+00:00
-- url     : https://prove2.me/submissions/c21916ac-a8ac-4517-b571-fb6d9d364ee8

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/LatticePaths.lean:L155-L172
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.lift_path. The node keeps its source
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
/-- Lifting a vertex path into a finite graph, retaining the exact endpoints. -/
theorem lift_path {r : Vertex → Vertex → Prop} {s : G.Node → G.Node → Prop}
    (hmem : ∀ x y, r x y → y ∈ G.vertices)
    (hrel : ∀ (x y : G.Node), r x.1 y.1 → s x y)
    {x y : G.Node} (h : Relation.ReflTransGen r x.1 y.1) : Relation.ReflTransGen s x y := by
  have hh : ∀ {z : Vertex}, Relation.ReflTransGen r x.1 z →
      ∀ hz : z ∈ G.vertices, Relation.ReflTransGen s x ⟨z,hz⟩ := by
    intro z hp
    induction hp with
    | refl => intro _; exact .refl
    | @tail a b ha hab ih =>
      intro hb
      rcases ha.cases_tail with hxa | ⟨u,hu,hua⟩
      · subst a
        exact Relation.ReflTransGen.single (hrel x ⟨b,hb⟩ hab)
      · have ham := hmem u a hua
        exact (ih ham).tail (hrel ⟨a,ham⟩ ⟨b,hb⟩ hab)
  exact hh h y.2

end LatticeGraph
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.lift_path := @_root_.OAI.CriticalZ3.LatticeGraph.lift_path
