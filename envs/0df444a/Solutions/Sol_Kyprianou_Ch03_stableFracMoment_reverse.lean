-- Prove2me | solution 1 for Kyprianou.Ch03.stableFracMoment_reverse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:47:50.792513+00:00
-- url     : https://prove2.me/submissions/08959b1b-00f2-4db8-9082-5063eb2c043e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_exercise33SubmultiplicativeExamples
import Theorems.Thm_Kyprianou_Ch03_submultiplicativeMomentsIffLargeJumpIntegral
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentMaxAbsIntegrableIffV1
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentMaxAbsLocallyBoundedV1
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentTailPowerIffV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha cPlus cMinus eta : ℝ)
    (hAlpha : 0 < alpha ∧ alpha < 2)
    (hCPlus : 0 ≤ cPlus) (hCMinus : 0 ≤ cMinus)
    (hNonzero : 0 < cPlus + cMinus)
    (hMeasure : T.levyMeasure =
      (volume : Measure ℝ).withDensity
        (fun x : ℝ => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0)))
    (hEta : 0 < eta) :
    (eta < alpha) -> ((∀ t : NNReal, 0 < t →
       Integrable (fun omega => |X t omega| ^ eta) P)) := by
  have hg := Kyprianou.Ch03.exercise33SubmultiplicativeExamples.2.2.2.1 eta hEta
  have criterion := Kyprianou.Ch03.submultiplicativeMomentsIffLargeJumpIntegral P X hX T hLK
    (fun x : ℝ => (max |x| 1)^eta) hg (by fun_prop)
    (Kyprianou.Ch03.stableFracMomentMaxAbsLocallyBoundedV1 eta hEta)
  have tail := Kyprianou.Ch03.stableFracMomentTailPowerIffV1 alpha cPlus cMinus eta
    hAlpha hCPlus hCMinus hNonzero hEta
  intro h
  have hl : IntegrableOn (fun x : ℝ => (max |x| 1)^eta) {x : ℝ | 1 ≤ |x|} T.levyMeasure := by
    rw [hMeasure]
    exact tail.mpr h
  intro t ht
  exact (Kyprianou.Ch03.stableFracMomentMaxAbsIntegrableIffV1 P (X t)
    (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t) eta hEta).mpr
    (criterion.mp hl t ht)
