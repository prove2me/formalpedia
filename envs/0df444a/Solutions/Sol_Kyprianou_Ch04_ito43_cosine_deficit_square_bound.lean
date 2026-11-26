-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_deficit_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:34:57.725276+00:00
-- url     : https://prove2.me/submissions/d01987ad-dd62-4860-898d-1a8df6f9aa48

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_cosine_bounds
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (a z : ℝ) (ha : 0 < a) :
    let q := (1-Real.cos (a*z))/a^2
    0 ≤ q ∧ q ≤ z^2/2 ∧ q ≤ 2/a^2 := by
  intro q
  have h := Kyprianou.Ch04.ito43_qv_cosine_bounds a z
  refine ⟨h.1,?_,h.2.1⟩
  apply (div_le_iff₀ (by positivity : 0 < a^2)).mpr
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := a*z)]
