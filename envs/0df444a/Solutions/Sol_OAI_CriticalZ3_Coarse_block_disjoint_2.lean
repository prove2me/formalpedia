-- Prove2me | solution 2 for OAI.CriticalZ3.Coarse.block_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:38:07.846253+00:00
-- url     : https://prove2.me/submissions/38986b44-c9ea-4865-94a9-0028c93858cb

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Coarse.lean:L260-L275
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Coarse.block_disjoint. The node keeps its source
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
theorem Q_disjoint (r : ℕ) {v w : Point} (h : v ≠ w) : Disjoint (Q r v).vertices (Q r w).vertices := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (cube_unique r ((Box.mem_vertices _ _).mp hx) ((Box.mem_vertices _ _).mp hy))

theorem interface_eq_endpoints (r : ℕ) {v w a b : Point} {e : Bond}
    (h : e ∈ interface r v w) (h' : e ∈ interface r a b) :
    (v = a ∧ w = b) ∨ (v = b ∧ w = a) := by
  rw [mem_interface] at h h'
  rcases h with h|h <;> rcases h' with h'|h'
  · exact Or.inl ⟨cube_unique r h.1 h'.1,cube_unique r h.2 h'.2⟩
  · exact Or.inr ⟨cube_unique r h.1 h'.1,cube_unique r h.2 h'.2⟩
  · exact Or.inr ⟨cube_unique r h.2 h'.2,cube_unique r h.1 h'.1⟩
  · exact Or.inl ⟨cube_unique r h.2 h'.2,cube_unique r h.1 h'.1⟩

theorem internal_not_interface (r : ℕ) {u v w : Point} (hvw : v ≠ w) :
    Disjoint (Q r u).bonds (interface r v w) := by
  refine Finset.disjoint_left.mpr ?_
  intro e he hi
  have hh := (Box.mem_bonds _ _).mp he
  rw [mem_interface] at hi
  rcases hi with hi|hi
  · exact hvw ((cube_unique r hi.1 hh.1).trans (cube_unique r hh.2 hi.2))
  · exact hvw ((cube_unique r hi.2 hh.2).trans (cube_unique r hh.1 hi.1))

end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

end LatticeGraph

namespace Coarse
theorem bits_disjoint (m : Model) (r : ℕ) {v w : Point} (h : v ≠ w) :
    Disjoint ((Q r v).bits m) ((Q r w).bits m) := by
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he hf
    exact h (cube_unique r ((Box.mem_bonds _ _).mp he).1 ((Box.mem_bonds _ _).mp hf).1)
  · exact Q_disjoint r h

theorem bits_link_disjoint (m : Model) (r : ℕ) (u : Point) {v w : Point} (h : v ≠ w) :
    Disjoint ((Q r u).bits m) (linkBits m r v w) := by
  cases m
  · exact internal_not_interface r h
  · exact Finset.disjoint_empty_right _

theorem block_disjoint (m : Model) (r : ℕ) {D : Finset Point} {v w a b : Point}
    (hv : v ∉ D) (hw : w ∉ D) (ha : a ∈ D) (hb : b ∈ D) (hvw : v ≠ w) :
    Disjoint (block m r v a) (block m r w b) := by
  have hva : v ≠ a := fun h => hv (h ▸ ha)
  have hwb : w ≠ b := fun h => hw (h ▸ hb)
  rw [block,block,Finset.disjoint_union_left,Finset.disjoint_union_right,
    Finset.disjoint_union_right]
  refine ⟨⟨bits_disjoint m r hvw,bits_link_disjoint m r v hwb⟩,
    ⟨(bits_link_disjoint m r w hva).symm,?_⟩⟩
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he hf
    rcases interface_eq_endpoints r he hf with h|h
    · exact hvw h.1
    · exact hv (h.1 ▸ hb)
  · exact Finset.disjoint_empty_left _

end Coarse
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.Coarse.block_disjoint := @_root_.OAI.CriticalZ3.Coarse.block_disjoint
