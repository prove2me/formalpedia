-- Prove2me | solution 2 for OAI.LatticeRelay.translation_face
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:09:39.578743+00:00
-- url     : https://prove2.me/submissions/21254035-6bdd-4a3b-8d43-c3590370532b

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Relay.lean:L113-L128
-- (upload_full_project.md Phase 4): solution for node OAI.LatticeRelay.translation_face. The node keeps its source
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
theorem inward_interval_bound {a b s W : ℤ} (hW : s ≤ W) (ha : |a| ≤ W)
    (hb : DirectedInterval a s (decide (a < 0)) b) : |b| ≤ W := by
  rw [abs_le] at ha ⊢
  by_cases h : a < 0 <;> simp [DirectedInterval,h] at hb <;> omega

/-- Generic form of each of the ten translation steps, including the final
length 2r+1 step. -/
theorem translation_face {a s w : ℤ} (hs : s ≤ w) {u : Vertex}
    (hu : u ∈ Cube (axisCenter a) w) :
    QuarterFace u s 0 (forwardInward u) ⊆ Cube (axisCenter (a+s)) w := by
  intro x hx i
  by_cases hi : i = 0
  · subst i
    have huu := hu 0
    rw [hx.1]
    simpa [forwardInward,axisCenter] using huu
  · have huu := hu i
    have hxx := hx.2 i hi
    simp only [forwardInward,hi,ite_false] at hxx
    simp only [axisCenter,hi,ite_false,sub_zero] at huu ⊢
    exact inward_interval_bound hs huu hxx

end LatticeRelay

end OAI

-- ---- platform node ----
open OAI OAI.LatticeRelay
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Set


theorem solution : type_of% @_root_.OAI.LatticeRelay.translation_face := @_root_.OAI.LatticeRelay.translation_face
