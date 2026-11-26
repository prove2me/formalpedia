-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_exponential_cell_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:26:25.415954+00:00
-- url     : https://prove2.me/submissions/e8640e3f-14f8-4114-b9e1-2ed199b4bbf2

import Mathlib.Analysis.Complex.Exponential
set_option autoImplicit false

/-- Right-point product correction expressed through the logarithmic increment. -/
theorem solution (eb ga gb : Complex) :
    Complex.exp eb * (Complex.exp gb - Complex.exp ga) =
      Complex.exp (eb + gb) * (1 - Complex.exp (-(gb - ga))) := by
  rw [mul_sub, mul_sub, mul_one]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring
