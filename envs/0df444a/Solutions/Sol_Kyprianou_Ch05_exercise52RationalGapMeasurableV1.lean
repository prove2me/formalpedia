-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52RationalGapMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:21:14.576022+00:00
-- url     : https://prove2.me/submissions/9ab5f526-b466-4098-b0e5-990ea19045b6

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- Countable intersections and unions of coordinate preimages give measurability. -/
theorem solution
    (x u y : ℝ) :
    MeasurableSet {g : NNReal → ℝ | ∃ a b : ℚ, (a : ℝ) < x - y ∧ x + u < (b : ℝ) ∧
      (∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)} := by
  classical
  have h1 (a b : ℚ) : MeasurableSet {g : NNReal → ℝ |
      ∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)} := by
    have h : {g : NNReal → ℝ |
        ∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)} =
        ⋂ q : ℚ, (fun g : NNReal → ℝ => g (Real.toNNReal q)) ⁻¹' (Iic (a : ℝ) ∪ Ici (b : ℝ)) := by
      ext g
      simp
    rw [h]
    exact MeasurableSet.iInter fun q => measurable_pi_apply _ (measurableSet_Iic.union measurableSet_Ici)
  have h2 (b : ℚ) : MeasurableSet {g : NNReal → ℝ | ∃ q : ℚ,
      (b : ℝ) ≤ g (Real.toNNReal q)} := by
    have h : {g : NNReal → ℝ | ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)} =
        ⋃ q : ℚ, (fun g : NNReal → ℝ => g (Real.toNNReal q)) ⁻¹' Ici (b : ℝ) := by
      ext g
      simp
    rw [h]
    exact MeasurableSet.iUnion fun q => measurable_pi_apply _ measurableSet_Ici
  have h : {g : NNReal → ℝ | ∃ a b : ℚ, (a : ℝ) < x - y ∧ x + u < (b : ℝ) ∧
      (∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)} =
      ⋃ a : ℚ, ⋃ b : ℚ, if (a : ℝ) < x-y ∧ x+u < (b : ℝ) then
        {g : NNReal → ℝ | ∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨
          (b : ℝ) ≤ g (Real.toNNReal q)} ∩
        {g : NNReal → ℝ | ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)}
      else ∅ := by
    ext g
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨a,b,ha,hb,hg,he⟩
      exact ⟨a,b,by simp [ha,hb,hg,he]⟩
    · rintro ⟨a,b,h⟩
      split at h
      · rename_i hab
        exact ⟨a,b,hab.1,hab.2,h.1,h.2⟩
      · exact (notMem_empty _ h).elim
  rw [h]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  split
  · exact (h1 a b).inter (h2 b)
  · exact MeasurableSet.empty
