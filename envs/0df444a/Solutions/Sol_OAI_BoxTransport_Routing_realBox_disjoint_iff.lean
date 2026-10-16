-- Prove2me | solution 1 for OAI.BoxTransport.Routing.realBox_disjoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:26:51.818809+00:00
-- url     : https://prove2.me/submissions/4b18f402-a1d5-47bd-8ba3-d96b5ef74a25

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Geometry.lean:L80-L113
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.realBox_disjoint_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry

-- ---- from OAI.Analysis.BoxTransport.Geometry ----
namespace OAI

/-! Quantitative box separation, affine images and positive diagonal shape estimates. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem realBox_disjoint_of_gap {c d h k : Space}
    (hgap : ∃ j, h j + k j < |c j - d j|) :
    Disjoint (realBox c h) (realBox d k) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j, hj⟩ := hgap
  have hle : |c j - d j| ≤ h j + k j := calc
    |c j - d j| = |(c j - x j) + (x j - d j)| := by congr 1; ring
    _ ≤ |c j - x j| + |x j - d j| := abs_add_le _ _
    _ = |x j - c j| + |x j - d j| := by rw [abs_sub_comm (c j) (x j)]
    _ ≤ h j + k j := add_le_add (hx j) (hy j)
  exact (not_lt_of_ge hle) hj

theorem realBox_disjoint_iff {c d h k : Space}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j) :
    Disjoint (realBox c h) (realBox d k) ↔
      ∃ j, h j + k j < |c j - d j| := by
  refine ⟨?_, realBox_disjoint_of_gap⟩
  intro hdis
  by_contra hn
  push Not at hn
  let x : Space := fun j => max (c j - h j) (d j - k j)
  have hx : x ∈ realBox c h := by
    intro j
    have hj := (abs_le.mp (hn j)).1
    have hwidth := hh j
    apply abs_le.mpr
    constructor
    · dsimp [x]
      have := le_max_left (c j - h j) (d j - k j)
      linarith
    · have hup : x j ≤ c j + h j := by
        apply max_le <;> linarith
      linarith
  have hy : x ∈ realBox d k := by
    intro j
    have hj := (abs_le.mp (hn j)).2
    have hwidth := hk j
    apply abs_le.mpr
    constructor
    · dsimp [x]
      have := le_max_right (c j - h j) (d j - k j)
      linarith
    · have hup : x j ≤ d j + k j := by
        apply max_le <;> linarith
      linarith
  exact (Set.disjoint_left.mp hdis) hx hy

end BoxTransport.Routing

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.realBox_disjoint_iff := @_root_.OAI.BoxTransport.Routing.realBox_disjoint_iff
