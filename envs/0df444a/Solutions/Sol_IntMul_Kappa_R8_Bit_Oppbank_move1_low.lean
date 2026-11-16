-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.move1_low
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:30:52.85362+00:00
-- url     : https://prove2.me/submissions/9e32edda-db06-4eb0-943b-001661ce62dc

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open Matrix

private theorem Pc_low' : Pc 0 = 0 := by simp [Pc]

private theorem K_zero_left (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (B : M23) : K S Si 0 B = 0 := by
  rw [K, Matrix.zero_kronecker, Matrix.mul_zero, Matrix.zero_mul]

private theorem pswQ_zero' {m : ℕ} : pswQ (0 : Matrix (Fin m) (Fin m) ℚ) = 1 := by
  unfold pswQ
  rw [sub_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

private theorem dimCF_zero : dimCF 0 = 0 := by simp [dimCF]

private theorem Dm_from_low (c : ℕ) : Dm 0 c = Pc c := by
  have hdim : dimCF 0 ≤ dimCF c := by simp [dimCF_zero]
  unfold Dm
  rw [if_pos hdim, Pc_low', sub_zero]

private theorem Φ₁_low (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (b : ℕ) : Φ₁ S Si b 0 = 1 := by
  rw [Φ₁, Pc_low', K_zero_left, pswQ_zero']

theorem solution (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    {c b : ℕ} (_hc : c < codeBound) (_hb : b < 1771) :
    pswQ (K S Si (Dm 0 c) (Pl b)) * Φ₁ S Si b 0 = Φ₁ S Si b c := by
  -- `dimCF 0 = 0 ≤ dimCF c`, so `Dm 0 c = Pc c`; the incoming frame is `I`.
  rw [Dm_from_low, Φ₁_low, Matrix.mul_one, Φ₁]
