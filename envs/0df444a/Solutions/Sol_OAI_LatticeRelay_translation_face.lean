-- Prove2me | solution 1 for OAI.LatticeRelay.translation_face
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:14:44.919989+00:00
-- url     : https://prove2.me/submissions/fbda95d8-0c63-42b0-b01e-c11f1a053856

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

open OAI OAI.LatticeRelay
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Set


theorem solution {a s w : ℤ} (hs : s ≤ w) {u : Vertex}
    (hu : u ∈ Cube (axisCenter a) w) :
    QuarterFace u s 0 (forwardInward u) ⊆ Cube (axisCenter (a+s)) w := by
  rintro x ⟨h0, hi⟩
  simp only [Cube, Rect, Set.mem_setOf_eq, axisCenter] at hu ⊢
  intro j
  by_cases hj : j = 0
  · subst hj
    have := hu 0
    simp only [forwardInward, if_true] at h0
    simp only [if_true] at this ⊢
    rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]
  · have hd := hi j hj
    have hu' := hu j
    simp only [hj, if_false, sub_zero] at hu' ⊢
    unfold DirectedInterval forwardInward at hd
    simp only [hj, if_false] at hd
    rw [abs_le] at hu' ⊢
    by_cases hneg : u j < 0
    · simp only [hneg, decide_true, if_true] at hd; constructor <;> omega
    · simp only [hneg, decide_false, Bool.false_eq_true, if_false] at hd; constructor <;> omega

