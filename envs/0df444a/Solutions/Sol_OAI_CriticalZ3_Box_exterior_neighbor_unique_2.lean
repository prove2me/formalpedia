-- Prove2me | solution 2 for OAI.CriticalZ3.Box.exterior_neighbor_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:21:15.551369+00:00
-- url     : https://prove2.me/submissions/881c17ea-a05e-4d81-b5b1-b82090c6b815

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/BoxGeometry.lean:L102-L130
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Box.exterior_neighbor_unique. The node keeps its source
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

-- ---- from OAI.Probability.CriticalZ3.BoxGeometry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

namespace Box

theorem neighbor_coordinates {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ i, |y i-x i| = 1 ∧ ∀ k, k ≠ i → y k = x k := by
  obtain ⟨i, h | h⟩ := h
  · subst y
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]
  · subst x
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]

/-- The uniqueness used by the shell-closing argument, including corners. -/
theorem exterior_neighbor_unique (B : Box) {y z z' : Vertex}
    (hy : ¬ B.Contains y) (hz : B.Contains z) (hz' : B.Contains z')
    (hyz : NearestNeighbor y z) (hyz' : NearestNeighbor y z') : z = z' := by
  obtain ⟨i,hi⟩ : ∃ i, ¬ (B.lower i ≤ y i ∧ y i ≤ B.upper i) := by
    simpa only [Contains,not_forall] using hy
  obtain ⟨j,hj,hej⟩ := neighbor_coordinates hyz
  obtain ⟨k,hk,hek⟩ := neighbor_coordinates hyz'
  have hij : i = j := by
    by_contra h
    have hh := hej i h
    have hh' := hz i
    omega
  have hik : i = k := by
    by_contra h
    have hh := hek i h
    have hh' := hz' i
    omega
  subst j; subst k
  funext l
  by_cases hl : l = i
  · subst l
    have hz0 := hz i
    have hz1 := hz' i
    have hj0 := hj.le
    have hk0 := hk.le
    rw [abs_le] at hj0 hk0
    omega
  · rw [hej l hl,hek l hl]

end Box
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.Box.exterior_neighbor_unique := @_root_.OAI.CriticalZ3.Box.exterior_neighbor_unique
