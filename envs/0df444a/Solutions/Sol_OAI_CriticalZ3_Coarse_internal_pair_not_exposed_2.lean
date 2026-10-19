-- Prove2me | solution 2 for OAI.CriticalZ3.Coarse.internal_pair_not_exposed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:40:55.479851+00:00
-- url     : https://prove2.me/submissions/2f7434d9-ba7a-44ae-bb14-2faa9eeea517

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Coarse.lean:L296-L346
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Coarse.internal_pair_not_exposed. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_Coarse_cube_unique

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
theorem internal_pair_not_exposed (m : Model) (r : ℕ) {D : Finset Point}
    (h0 : 0 ∈ D) {v w : Point} (hv : v ∉ D) (hw : w ∉ D) {e : m.Bit}
    (he : m.Internal (PairRegion r v w) e) : e ∉ exposed m r D := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ h0)
  have hw0 : w ≠ 0 := fun h => hw (h ▸ h0)
  cases m
  · change e ∉ _
    rw [internal_pair_bond] at he
    simp only [Finset.mem_union] at he
    simp only [exposed,rootBits,linkBits,Box.bits,Finset.mem_union,Finset.mem_biUnion,
      Finset.mem_product,Finset.mem_univ,true_and]
    intro hb
    have noInternal (a : Point) (ha : a ∈ D) (h : e ∈ (Q r a).bonds) : False := by
      have hl := ((Box.mem_bonds _ _).mp h).1
      rcases he with (he|he)|he
      · exact hv ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
      · exact hw ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
      · rcases (mem_interface r v w e).mp he with he|he
        · exact hv ((cube_unique r he.1 hl) ▸ ha)
        · exact hw ((cube_unique r he.1 hl) ▸ ha)
    have noLink (a b : Point) (ha : a ∈ D) (h : e ∈ interface r a b) : False := by
      rcases (mem_interface r a b e).mp h with h|h
      · have hl := h.1
        rcases he with (he|he)|he
        · exact hv ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
        · exact hw ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
        · rcases (mem_interface r v w e).mp he with he|he
          · exact hv ((cube_unique r he.1 hl) ▸ ha)
          · exact hw ((cube_unique r he.1 hl) ▸ ha)
      · have hl := h.2
        rcases he with (he|he)|he
        · exact hv ((cube_unique r ((Box.mem_bonds _ _).mp he).2 hl) ▸ ha)
        · exact hw ((cube_unique r ((Box.mem_bonds _ _).mp he).2 hl) ▸ ha)
        · rcases (mem_interface r v w e).mp he with he|he
          · exact hw ((cube_unique r he.2 hl) ▸ ha)
          · exact hv ((cube_unique r he.2 hl) ▸ ha)
    rcases hb with ((hb|⟨d,hd⟩)|⟨a,ha,hb⟩)|⟨⟨a,b⟩,⟨ha,_⟩,hb⟩
    · exact noInternal 0 h0 hb
    · exact noLink 0 (outward d) h0 hd
    · exact noInternal a ha hb
    · exact noLink a b ha hb
  · change (Q r v).Contains e ∨ (Q r w).Contains e at he
    simp only [exposed,rootBits,linkBits,Box.bits,Finset.mem_union,Finset.mem_biUnion,
      Box.mem_vertices,Finset.notMem_empty,and_false,exists_false,or_false]
    rintro (hh|⟨a,ha,hh⟩)
    · rcases he with he|he
      · exact hv0 (cube_unique r he hh)
      · exact hw0 (cube_unique r he hh)
    · rcases he with he|he
      · exact hv ((cube_unique r he hh) ▸ ha)
      · exact hw ((cube_unique r he hh) ▸ ha)

end Coarse
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.Coarse.internal_pair_not_exposed := @_root_.OAI.CriticalZ3.Coarse.internal_pair_not_exposed
