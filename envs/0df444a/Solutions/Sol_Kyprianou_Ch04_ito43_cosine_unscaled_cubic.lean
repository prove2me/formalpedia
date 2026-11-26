-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_unscaled_cubic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:28:46.430717+00:00
-- url     : https://prove2.me/submissions/60106f76-30dc-4356-a929-f37023036251

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_second_derivative
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_taylor_modulus
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (x : ℝ) :
    |Real.cos x-1+x^2/2| ≤ |x| * x^2/2 := by
  have hb (z : ℝ) (hz : z ∈ uIcc 0 x) :
      |iteratedDeriv 2 Real.cos z-(-1)| ≤ |x| := by
    rw [Kyprianou.Ch04.ito43_cosine_second_derivative]
    have hz' : |z| ≤ |x| := by
      rw [mem_uIcc] at hz
      rcases hz with h|h
      · rw [abs_of_nonneg h.1,abs_of_nonneg (h.1.trans h.2)]
        exact h.2
      · rw [abs_of_nonpos h.2,abs_of_nonpos (h.1.trans h.2)]
        linarith [h.1]
    have hc := Real.abs_cos_sub_cos_le z 0
    rw [Real.cos_zero,sub_zero] at hc
    calc
      |(-Real.cos z)-(-1)| = |Real.cos z-1| := by rw [← abs_neg]; congr 1; ring
      _ ≤ |z| := hc
      _ ≤ |x| := hz'
  have h := Kyprianou.Ch04.ito43_spatial_taylor_modulus Real.cos
    Real.contDiff_cos 0 x (-1) |x| (abs_nonneg x) hb
  rw [(Real.hasDerivAt_cos 0).deriv,Real.sin_zero,Real.cos_zero] at h
  simpa only [neg_zero,zero_mul,sub_zero,neg_one_mul,neg_div,sub_neg_eq_add] using h
