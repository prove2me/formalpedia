-- Prove2me | solution 1 for Kyprianou.Ch01.discountedPut_pointwiseBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:55:01.942569+00:00
-- url     : https://prove2.me/submissions/237b5994-0dc8-4b19-859a-4a07c56a57de

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (x K q : ℝ)
    (hK : 0 < K) (hq : 0 < q)
    (tau : Ω → WithTop ℝ≥0) (omega : Ω) :
    0 ≤ discountedPut X x K q tau omega ∧
      discountedPut X x K q tau omega ≤ K := by
  cases htime : tau omega with
  | top =>
      simp [discountedPut, htime, hK.le]
  | coe t =>
      have ht : 0 ≤ (t : ℝ) := NNReal.coe_nonneg _
      have hdisc : 0 ≤ Real.exp (-q * (t : ℝ)) :=
        (Real.exp_pos _).le
      have hdiscLe : Real.exp (-q * (t : ℝ)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [mul_nonneg hq.le ht]
      have hpayNonneg :
          0 ≤ max (K - Real.exp (x + X t omega)) 0 :=
        le_max_right _ _
      have hpayLe :
          max (K - Real.exp (x + X t omega)) 0 ≤ K := by
        apply max_le
        · linarith [Real.exp_pos (x + X t omega)]
        · exact hK.le
      simp only [discountedPut, htime]
      constructor
      · exact mul_nonneg hdisc hpayNonneg
      · calc
          Real.exp (-q * (t : ℝ)) *
              max (K - Real.exp (x + X t omega)) 0 ≤
              1 * max (K - Real.exp (x + X t omega)) 0 :=
              mul_le_mul_of_nonneg_right hdiscLe hpayNonneg
          _ ≤ K := by simpa using hpayLe
