-- Prove2me | solution 2 for OAI.LatticeRelay.contraction_face
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:08:08.295138+00:00
-- url     : https://prove2.me/submissions/7fc9f4cc-37ee-44d4-b904-2f32c3085163

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Relay.lean:L65-L86
-- (upload_full_project.md Phase 4): solution for node OAI.LatticeRelay.contraction_face. The node keeps its source
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

-- ---- from OAI.Probability.CriticalZ3.Relay ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace LatticeRelay
open Set
theorem inward_endpoint_bound {a s W : ℤ} (_hs : 0 ≤ s) (hW : s ≤ W)
    (ha : |a| ≤ W+s) : |a + (if decide (a < 0) then s else -s)| ≤ W := by
  rw [abs_le] at ha ⊢
  by_cases h : a < 0 <;> simp [h] <;> omega

theorem inward_interval_bound {a b s W : ℤ} (hW : s ≤ W) (ha : |a| ≤ W)
    (hb : DirectedInterval a s (decide (a < 0)) b) : |b| ≤ W := by
  rw [abs_le] at ha ⊢
  by_cases h : a < 0 <;> simp [DirectedInterval,h] at hb <;> omega

/-- Generic form of one of the three contraction steps. -/
theorem contraction_face {r a : ℤ} (hr : 0 ≤ r) (ha : 0 ≤ a) (h : Fin 3)
    {u : Vertex}
    (hu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a) :
    QuarterFace u (2*r) h (inward u) ⊆
      Rect 0 (fun i => if i ≤ h then 2*r+a else 4*r+a) := by
  intro x hx i
  change |x i - 0| ≤ _
  rw [sub_zero]
  by_cases hi : i = h
  · subst i
    rw [hx.1]
    simp only [le_refl,ite_true,inward]
    apply inward_endpoint_bound (by omega) (by omega)
    have huu := hu h
    simp only [lt_self_iff_false,ite_false] at huu
    omega
  · have hh := hx.2 i hi
    dsimp [inward] at hh
    apply inward_interval_bound (by dsimp; split_ifs <;> omega) _ hh
    have hhi : (i < h) ↔ (i ≤ h) := by omega
    simpa only [hhi] using hu i

end LatticeRelay

end OAI

-- ---- platform node ----
open OAI OAI.LatticeRelay
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Set


theorem solution : type_of% @_root_.OAI.LatticeRelay.contraction_face := @_root_.OAI.LatticeRelay.contraction_face
