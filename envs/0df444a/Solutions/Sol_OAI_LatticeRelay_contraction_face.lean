-- Prove2me | solution 1 for OAI.LatticeRelay.contraction_face
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:14:52.363992+00:00
-- url     : https://prove2.me/submissions/f2952ba7-86c0-418d-8b66-cea4fa01b4a3

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


theorem solution {r a : ℤ} (hr : 0 ≤ r) (ha : 0 ≤ a) (h : Fin 3)
    {u : Vertex}
    (hu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a) :
    QuarterFace u (2*r) h (inward u) ⊆
      Rect 0 (fun i => if i ≤ h then 2*r+a else 4*r+a) := by
  rintro x ⟨hn, hi⟩
  simp only [Rect, Set.mem_setOf_eq, Pi.zero_apply, sub_zero]
  intro i
  by_cases hih : i = h
  · subst hih
    have hu' := hu i
    simp only [lt_irrefl, if_false] at hu'
    simp only [le_refl, if_true]
    unfold inward at hn
    rw [abs_le] at hu' ⊢
    by_cases hneg : u i < 0
    · simp only [hneg, decide_true, if_true] at hn; constructor <;> omega
    · simp only [hneg, decide_false, Bool.false_eq_true, if_false] at hn; constructor <;> omega
  · have hd := hi i hih
    have hu' := hu i
    unfold DirectedInterval inward at hd
    have hcase : (i < h ∧ i ≤ h) ∨ (¬ i < h ∧ ¬ i ≤ h) := by
      rcases lt_or_gt_of_ne hih with h1 | h1
      · exact Or.inl ⟨h1, h1.le⟩
      · exact Or.inr ⟨not_lt.mpr h1.le, not_le.mpr h1⟩
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2, if_true] at hu' ⊢
      rw [abs_le] at hu' ⊢
      by_cases hneg : u i < 0
      · simp only [hneg, decide_true, if_true] at hd; constructor <;> omega
      · simp only [hneg, decide_false, Bool.false_eq_true, if_false] at hd; constructor <;> omega
    · simp only [h1, h2, if_false] at hu' ⊢
      rw [abs_le] at hu' ⊢
      by_cases hneg : u i < 0
      · simp only [hneg, decide_true, if_true] at hd; constructor <;> omega
      · simp only [hneg, decide_false, Bool.false_eq_true, if_false] at hd; constructor <;> omega

