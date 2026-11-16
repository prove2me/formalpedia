-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.K_mul
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:30:52.282926+00:00
-- url     : https://prove2.me/submissions/c72956f8-e7b7-4389-a918-5ba077882c9c

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open scoped Kronecker
open Matrix
theorem solution (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) (A B C D : M23) :
    K S Si A B * K S Si C D = K S Si (A * C) (B * D) := by
  simp only [K, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Si S, hSi, Matrix.one_mul, ← Matrix.mul_assoc (A ⊗ₖ B),
    ← Matrix.mul_kronecker_mul]
