-- Prove2me | solution 2 for OAI.CriticalZ3.LatticeGraph.bondConn_iff_hypergraph
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:16:15.972958+00:00
-- url     : https://prove2.me/submissions/af26bb27-71e5-4cf7-8add-71dc1f8616b7

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/LatticeGraph.lean:L118-L142
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.bondConn_iff_hypergraph. The node keeps its source
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

-- ---- from OAI.Probability.CriticalZ3.LatticeGraph ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open Classical MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory

namespace LatticeGraph
variable (G : LatticeGraph)

theorem bondConn_iff_hypergraph (ω : BondConfig) (x y : G.Node) :
    G.BondConn ω x y ↔ HyperedgeComparison.Connected G.hypergraph
      (fun e => ω e.1) ∅ x y := by
  constructor
  · intro h
    apply Relation.ReflTransGen.mono (r := G.BondAdj ω) (p := _) ?_ x y h
    intro a b hab
    obtain ⟨e,he,hxy,ho⟩ := hab
    refine ⟨⟨e,he⟩,ho,Set.disjoint_empty _,?_,?_⟩
    · rcases hxy with ⟨h,_⟩ | ⟨_,h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases hxy with ⟨_,h⟩ | ⟨h,_⟩
      · exact Or.inr h
      · exact Or.inl h
  · intro h
    induction h with
    | refl => exact .refl
    | @tail a b _ hab ih =>
      obtain ⟨e,ho,_,ha,hb⟩ := hab
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact (Subtype.ext (ha.trans hb.symm)) ▸ ih
      · exact ih.tail ⟨e.1,e.2,Or.inl ⟨ha,hb⟩,ho⟩
      · exact ih.tail ⟨e.1,e.2,Or.inr ⟨hb,ha⟩,ho⟩
      · exact (Subtype.ext (ha.trans hb.symm)) ▸ ih

end LatticeGraph
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical MeasureTheory ProbabilityTheory


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.bondConn_iff_hypergraph := @_root_.OAI.CriticalZ3.LatticeGraph.bondConn_iff_hypergraph
