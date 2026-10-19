-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.lift_path
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:35:59.89366+00:00
-- url     : https://prove2.me/submissions/0d18fb4e-f24c-4606-bd82-b29a028b46f7

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

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical
variable (G : LatticeGraph)


theorem solution {r : Vertex → Vertex → Prop} {s : G.Node → G.Node → Prop}
    (hmem : ∀ x y, r x y → y ∈ G.vertices)
    (hrel : ∀ (x y : G.Node), r x.1 y.1 → s x y)
    {x y : G.Node} (h : Relation.ReflTransGen r x.1 y.1) : Relation.ReflTransGen s x y := by
  have key : ∀ b, Relation.ReflTransGen r x.1 b →
      ∃ hb : b ∈ G.vertices, Relation.ReflTransGen s x ⟨b, hb⟩ := by
    intro b hb
    induction hb with
    | refl => exact ⟨x.2, Relation.ReflTransGen.refl⟩
    | @tail c b _ hcb ih =>
      obtain ⟨hc, hxc⟩ := ih
      exact ⟨hmem c b hcb, hxc.tail (hrel ⟨c, hc⟩ ⟨b, hmem c b hcb⟩ hcb)⟩
  obtain ⟨_, h'⟩ := key y.1 h
  exact h'

