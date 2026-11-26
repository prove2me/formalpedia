-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52IntegratedTailProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:23:10.794894+00:00
-- url     : https://prove2.me/submissions/d3be7fd7-d7c5-4973-8ef4-1e2156b3df4d

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
/-- The normalised integrated-tail density is a probability law. -/
theorem solution
    (nu : Measure ℝ) (m : ℝ) (hm : 0 < m)
    (hMass : m = ∫ z in Ioi (0 : ℝ), (nu (Ioi z)).toReal ∂volume) :
    IsProbabilityMeasure (ascendingRecordJumpDistribution nu m) := by
  let f : ℝ → ℝ := fun z => (nu (Ioi z)).toReal
  have hInt : Integrable f (volume.restrict (Ioi 0)) := by
    by_contra hn
    have hz := integral_undef hn
    change m = ∫ z, f z ∂(volume.restrict (Ioi 0)) at hMass
    rw [hz] at hMass
    linarith
  have hNonneg (z : ℝ) : 0 ≤ f z / m :=
    div_nonneg ENNReal.toReal_nonneg hm.le
  have hMass' : ∫ z, f z / m ∂(volume.restrict (Ioi 0)) = 1 := by
    rw [integral_div, ← hMass, div_self hm.ne']
  constructor
  change ((volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun z => ENNReal.ofReal (f z / m))) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hInt.div_const m) (Eventually.of_forall hNonneg),
    hMass', ENNReal.ofReal_one]
