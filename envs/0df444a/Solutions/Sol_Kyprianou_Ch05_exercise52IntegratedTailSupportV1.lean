-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52IntegratedTailSupportV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:23:40.114518+00:00
-- url     : https://prove2.me/submissions/fb289518-cb11-4075-bd68-4f70032fa056

import Mathlib
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
/-- The integrated-tail law has positive support and is nonlattice if normalised. -/
theorem solution
    (nu : Measure ℝ) (m : ℝ)
    (hF : IsProbabilityMeasure (ascendingRecordJumpDistribution nu m)) :
    ascendingRecordJumpDistribution nu m (Iic 0) = 0 ∧
      NonLatticeMeasure (ascendingRecordJumpDistribution nu m) := by
  let F := ascendingRecordJumpDistribution nu m
  letI : IsProbabilityMeasure F := hF
  let R : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ENNReal := fun z => ENNReal.ofReal ((nu (Ioi z)).toReal / m)
  have hFz (s : Set ℝ) (hs : R s = 0) : F s = 0 :=
    withDensity_absolutelyContinuous R f hs
  constructor
  · apply hFz
    rw [Measure.restrict_apply measurableSet_Iic]
    have h : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by ext z; simp [not_lt_of_ge]
    rw [h, measure_empty]
  · intro h hh
    let A : Set ℝ := range (fun n : ℤ => (n : ℝ) * h)
    have hAc : A.Countable := countable_range _
    have hAz : R A = 0 := by
      apply le_antisymm
      exact ((Measure.restrict_le_self : R ≤ volume) A).trans (hAc.measure_zero volume).le
      exact bot_le
    have hFA := hFz A hAz
    have hEq : {x : ℝ | ∀ n : ℤ, x ≠ (n : ℝ) * h} = Aᶜ := by
      ext x
      simp [A, eq_comm]
    rw [hEq, measure_compl hAc.measurableSet (by rw [hFA]; exact ENNReal.zero_ne_top),
      hFA, measure_univ, tsub_zero]
    exact one_ne_zero
