-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49CounterexampleFromAdmissibleModelV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:54:07.593086+00:00
-- url     : https://prove2.me/submissions/3a394ef0-03a8-42b6-bfde-ef6afc3f492c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49CountableCocountableSpaceV3
import Theorems.Thm_Kyprianou_Ch04_exercise49ExpClockNonmeasurableV3
import Theorems.Thm_Kyprianou_Ch04_exercise49CounterexampleFromSpikeExtensionV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hLevy : IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : ℝ),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : ℝ)
    (hDrift : drift = triplet.drift - ∫ y in Ioo (-1 : ℝ) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSub : ¬ (∀ᵐ w ∂P, Monotone (fun t : NNReal => X t w)))
    (hInfinity : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop) :
    ¬ certificate_ex4_9_iii := by
  obtain ⟨m,hm⟩ := exercise49CountableCocountableSpaceV3 (E := ULift.{0} ℝ)
  letI : MeasurableSpace (ULift.{0} ℝ) := m
  obtain ⟨a,ha,hBad⟩ := exercise49ExpClockNonmeasurableV3 hm
  exact exercise49CounterexampleFromSpikeExtensionV3 P X hLevy triplet hTriplet hBV drift hDrift hd
    hNotSub hInfinity a ha hBad
