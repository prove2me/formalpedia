-- Prove2me | solution 1 for Kyprianou.Ch04.normalisedWeightStateBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:36:37.796621+00:00
-- url     : https://prove2.me/submissions/63747ae2-06b3-4c6b-966d-942f47ede855

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_positiveLeftDifferenceBoundV1
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- The normalised positive-time left weights inherit the compact state bound. -/
theorem solution (Y Z L U : NNReal → ℝ) (T : NNReal)
    (g : ℝ → ℝ → ℝ) (K d : ℝ) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hY : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (hZ : ∀ t, 0 < t → Tendsto Z (nhdsWithin t (Iio t)) (nhds (U t)))
    (hb : ∀ t ≤ T, |Y t-Z t| ≤ d)
    (hLip : ∀ s : NNReal, ∀ x y : ℝ, |g s x-g s y| ≤ K*|x-y|) :
    ∀ t ≤ T, |(if t=0 then 0 else g t (L t))-
      (if t=0 then 0 else g t (U t))| ≤ K*d := by
  intro t ht
  by_cases h0 : t = 0
  · simp [h0,mul_nonneg hK hd]
  simp only [if_neg h0]
  exact (hLip t _ _).trans (mul_le_mul_of_nonneg_left
    (Kyprianou.Ch04.positiveLeftDifferenceBoundV1 Y Z L U T d hY hZ hb t ht
      (pos_iff_ne_zero.mpr h0)) hK)
