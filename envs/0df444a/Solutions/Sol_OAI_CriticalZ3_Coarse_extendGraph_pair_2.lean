-- Prove2me | solution 2 for OAI.CriticalZ3.Coarse.extendGraph_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:42:38.723538+00:00
-- url     : https://prove2.me/submissions/c3ed20c3-6edb-4fda-905c-a3f10260a9ee

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Coarse.lean:L387-L400
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Coarse.extendGraph_pair. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse

-- ---- from OAI.Probability.CriticalZ3.Coarse ----
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Coarse
theorem internal_pair_bond (r : ℕ) (v w : Point) (e : Bond) :
    Model.Internal .bond (PairRegion r v w) e ↔
      e ∈ (Q r v).bonds ∪ (Q r w).bonds ∪ interface r v w := by
  simp only [Model.Internal,PairRegion,Set.mem_ofPred_eq,Finset.mem_union,Box.mem_bonds,mem_interface]
  tauto

end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

end LatticeGraph

namespace Coarse
theorem extendGraph_pair (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : (extendGraph r G v x hv).ContainsSet (PairRegion r v x) := by
  constructor
  · intro y hy
    rcases hy with hy|hy
    · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr hy))
    · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr hy)
  · intro e he hf
    have hh := (internal_pair_bond r v x e).mp ⟨he,hf⟩
    rcases Finset.mem_union.mp hh with hh|hh
    · rcases Finset.mem_union.mp hh with hh|hh
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hv.2 hh))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hh)
    · exact Finset.mem_union_right _ hh
end Coarse
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.Coarse.extendGraph_pair := @_root_.OAI.CriticalZ3.Coarse.extendGraph_pair
