-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RecoveryIndicatorProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:08:22.49861+00:00
-- url     : https://prove2.me/submissions/1bbaaac5-7d4c-416e-8e22-49a3cd1673c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → WithTop NNReal) (hB : Measurable B)
    (q : Real)
    (hTransform : (∫ w, if B w = ⊤ then (0 : Real) else
      Real.exp (-(0 : Real) * (((B w).untopD 0 : NNReal) : Real)) ∂P) = q) :
    (P {w | B w ≠ ⊤}).toReal = q := by
  classical
  let D : Set Omega := {w | B w ≠ ⊤}
  have hD : MeasurableSet D := (hB (measurableSet_singleton (⊤ : WithTop NNReal))).compl
  have he : (fun w => if B w = ⊤ then (0 : Real) else
      Real.exp (-(0 : Real) * (((B w).untopD 0 : NNReal) : Real))) =
      D.indicator (fun _ => (1 : Real)) := by
    funext w
    by_cases hw : B w = ⊤
    · simp [D, hw]
    · simp [D, hw]
  rw [he, integral_indicator hD, setIntegral_const, smul_eq_mul, mul_one] at hTransform
  exact hTransform
