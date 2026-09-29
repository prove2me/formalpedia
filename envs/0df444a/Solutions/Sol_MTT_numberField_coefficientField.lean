-- Prove2me | solution 1 for MTT.numberField_coefficientField
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-20T08:20:29.167735+00:00
-- url     : https://prove2.me/submissions/5d72e2d4-d3df-4541-bf3b-ab2eb7bddb57

import Theorems.Thm_MTT_Eigenform_coefficientField_finiteDimensional
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false
noncomputable section

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    NumberField f.coefficientField := by
  let _ : FiniteDimensional ℚ f.coefficientField :=
    MTT.Eigenform.coefficientField_finiteDimensional hN hk ι f
  exact NumberField.of_module_finite ℚ f.coefficientField
