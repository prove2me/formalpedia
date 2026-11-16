-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.goodK
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:16:18.936197+00:00
-- url     : https://prove2.me/submissions/0eda90ed-3906-407a-bcb6-433a1c6d6caf

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open IntMul.Kappa.R6.Bit
open AModelFac
open Matrix

variable {l n p : Type*} [Fintype l] [Fintype n] [Fintype p]

private theorem goodM_mul {N : ℕ} {A : Matrix l n ℚ} {B : Matrix n p ℚ}
    (hA : GoodM N A) (hB : GoodM N B) : GoodM N (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (goodSub N).sum_mem fun k _ => (goodSub N).mul_mem (hA i k) (hB k j)

private theorem goodM_kron {N : ℕ} {l' p' : Type*} [Fintype l'] [Fintype p']
    {A : Matrix l p ℚ} {B : Matrix l' p' ℚ}
    (hA : GoodM N A) (hB : GoodM N B) :
    GoodM N (Matrix.kroneckerMap (· * ·) A B) :=
  fun i j => (goodSub N).mul_mem (hA i.1 j.1) (hB i.2 j.2)

theorem solution {S : Matrix (Fin 529) Pr23 ℚ} {Si : Matrix Pr23 (Fin 529) ℚ} {N : ℕ}
    (hS : GoodM N S) (hSi : GoodM N Si) {A B : M23}
    (hA : GoodM N A) (hB : GoodM N B) : GoodM N (K S Si A B) :=
  goodM_mul (goodM_mul hS (goodM_kron hA hB)) hSi
