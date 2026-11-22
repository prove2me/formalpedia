-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedPutContactAboveBarrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:25:34.065367+00:00
-- url     : https://prove2.me/submissions/c9531ec4-c7bf-4175-8e51-43974b6382bd

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstLowerPassageEqShiftedNegUpperPublic
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageContinuousContactAtFiniteTimeMcKean

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (x barrier K q : ℝ)
    (hxb : barrier < x) (hK : Real.exp barrier ≤ K)
    (hContinuous : Continuous (fun t : ℝ≥0 => X t ω))
    (hStart : X 0 ω = 0) :
    discountedPut X x K q (firstLowerPassage X x barrier) ω =
      (K - Real.exp barrier) *
        passageLaplace (firstLowerPassage X x barrier) q ω := by
  classical
  cases hτ : firstLowerPassage X x barrier ω with
  | top =>
      simp [discountedPut, passageLaplace, hτ]
  | coe t =>
      have hpass :
          firstUpperPassage (fun u ξ => -X u ξ) (x - barrier) ω =
            (t : WithTop ℝ≥0) := by
        rw [← Kyprianou.Ch01.firstLowerPassageEqShiftedNegUpperPublic
          X x barrier]
        exact hτ
      have hnegcont : Continuous (fun u : ℝ≥0 => -X u ω) :=
        hContinuous.neg
      have hnegzero : -X 0 ω = (0 : ℝ) := by
        rw [hStart]
        ring
      have hcontact :=
        Kyprianou.Ch01.firstUpperPassageContinuousContactAtFiniteTimeMcKean
          (fun u ξ => -X u ξ) ω (x - barrier)
          (sub_pos.mpr hxb) hnegcont hnegzero t hpass
      have hvalue : x + X t ω = barrier := by
        linarith
      simp [discountedPut, passageLaplace, hτ, hvalue,
        max_eq_left (sub_nonneg.mpr hK), mul_comm]
