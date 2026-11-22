-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanExpectedPutAboveBarrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:28:09.518237+00:00
-- url     : https://prove2.me/submissions/00f7cfe7-dbca-47cd-ac35-0564e0cd2b5e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedLowerPassageAboveBarrier
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedPutContactAboveBarrier

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x barrier : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hxb : barrier < x) (hKbarrier : Real.exp barrier ≤ K)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    Integrable (discountedPut X x K q (firstLowerPassage X x barrier)) P ∧
      (∫ ω, discountedPut X x K q (firstLowerPassage X x barrier) ω ∂P) =
        (K - Real.exp barrier) *
          Real.exp (-(x - barrier) *
            ((Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
              sigma ^ 2)) := by
  have hLaplace :=
    Kyprianou.Ch01.mckeanDiscountedLowerPassageAboveBarrier
      P X sigma gamma q x barrier hsigma hq hxb.le hB hXmeas
  have hstart (ω : Ω) : X 0 ω = 0 := by
    simpa using congrFun hB.1.start_zero ω
  have hfun :
      discountedPut X x K q (firstLowerPassage X x barrier) =
        (fun ω => (K - Real.exp barrier) *
          passageLaplace (firstLowerPassage X x barrier) q ω) := by
    funext ω
    exact Kyprianou.Ch01.mckeanDiscountedPutContactAboveBarrier
      X ω x barrier K q hxb hKbarrier (hAllContinuous ω) (hstart ω)
  rw [hfun]
  constructor
  · exact hLaplace.1.const_mul _
  · rw [integral_const_mul, hLaplace.2]
