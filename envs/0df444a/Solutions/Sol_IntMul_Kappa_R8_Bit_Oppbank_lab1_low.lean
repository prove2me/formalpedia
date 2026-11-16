-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.lab1_low
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:16:18.453222+00:00
-- url     : https://prove2.me/submissions/840b23fa-f512-4c5d-8c33-d24b10375552

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
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open AModelFac
open Matrix

private theorem K_zero_left (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (B : M23) : K S Si 0 B = 0 := by
  rw [K, Matrix.zero_kronecker, Matrix.mul_zero, Matrix.zero_mul]

private theorem redHom_apply (N : ℕ) (r : goodSub N) : redHom N r = redFun N r := rfl

private theorem toGood_val {N : ℕ} {r : ℚ} (h : Nat.Coprime r.den N) :
    (toGood N r : ℚ) = r := by
  rw [toGood, dif_pos h]

private theorem redQ_eq {N : ℕ} {r : ℚ} (h : Nat.Coprime r.den N) :
    redQ N r = redFun N r := by
  simp only [redQ, toGood, dif_pos h, redHom_apply]

private theorem redQ_intCast (N : ℕ) (z : ℤ) : redQ N z = z := by
  have hc : Nat.Coprime ((z : ℚ).den) N := by simp
  rw [redQ_eq hc]
  simpa using redFun_spec hc z 1 (by simp)

private theorem redQ_zero (N : ℕ) : redQ N 0 = 0 := by
  simpa using redQ_intCast N 0

private theorem redM_one (N : ℕ) : redM N (1 : QMat2 529) = 1 := by
  ext i j
  rw [redM, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · simpa using redQ_intCast N 1
  · exact redQ_zero N

private theorem Pc_low' : Pc 0 = 0 := by simp [Pc]

private theorem pswQ_zero' {m : ℕ} : pswQ (0 : Matrix (Fin m) (Fin m) ℚ) = 1 := by
  unfold pswQ
  rw [sub_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem solution (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (N b : ℕ) : lab1 S Si N b cLOW = 1 := by
  rw [lab1, Φ₁, cLOW_eq, Pc_low', K_zero_left, pswQ_zero', redM_one]
