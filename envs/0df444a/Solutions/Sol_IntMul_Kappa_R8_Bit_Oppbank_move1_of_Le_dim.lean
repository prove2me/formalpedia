-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.move1_of_Le_dim
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:42:11.166853+00:00
-- url     : https://prove2.me/submissions/51b3c7ea-bf17-4971-ac8c-dd14d7cb7bf5

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open scoped Kronecker
open Matrix

private theorem Pl_eq_ProjB (T : ℕ) : Pl T = ProjB.Pl T := by
  unfold Pl ProjB.Pl xv ProjB.xv yv ProjB.yv tvQ ProjB.tvQ
  unfold triL ProjB.tri ptsL ProjB.pts fieldOf ProjB.fieldOf
  rfl

private theorem Pl_idem' {T : ℕ} (hT : T < 1771) : Pl T * Pl T = Pl T := by
  rw [Pl_eq_ProjB T]
  exact NetFB.Pl_idem hT

private theorem K_mul' (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) (A B C D : M23) :
    K S Si A B * K S Si C D = K S Si (A * C) (B * D) := by
  simp only [K, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Si S, hSi, Matrix.one_mul, ← Matrix.mul_assoc (A ⊗ₖ B),
    ← Matrix.mul_kronecker_mul]

private theorem K_add_left' (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (A A' B : M23) : K S Si (A + A') B = K S Si A B + K S Si A' B := by
  rw [K, K, K, Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]

private theorem K_sub_left' (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (A A' B : M23) : K S Si (A - A') B = K S Si A B - K S Si A' B := by
  rw [eq_sub_iff_add_eq, ← K_add_left', sub_add_cancel]

private theorem K_two_left' (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (A B : M23) : 2 * K S Si A B = K S Si (2 * A) B := by
  rw [two_mul, two_mul, K_add_left']

private theorem pswQ_mul' {m : ℕ} (p p' : Matrix (Fin m) (Fin m) ℚ) :
    pswQ p * pswQ p' = pswQ (p + p' - 2 * (p * p')) := by
  unfold pswQ
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  congr 1 <;> noncomm_ring

private theorem rewrite_frame (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) {b : ℕ} (hb : b < 1771) (D Q : M23) :
    pswQ (K S Si D (Pl b)) * pswQ (K S Si Q (Pl b)) =
      pswQ (K S Si (D + Q - 2 * (D * Q)) (Pl b)) := by
  rw [pswQ_mul', K_mul' S Si hSi, Pl_idem' hb, K_two_left', ← K_add_left', ← K_sub_left']

theorem solution (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) {o c b : ℕ} (ho : o < codeBound) (_hc : c < codeBound)
    (hb : b < 1771)
    (h : (dimCF o ≤ dimCF c ∧ Le (Pc o) (Pc c)) ∨
         (¬ dimCF o ≤ dimCF c ∧ Le (Pc c) (Pc o))) :
    pswQ (K S Si (Dm o c) (Pl b)) * Φ₁ S Si b o = Φ₁ S Si b c := by
  rcases h with ⟨hdim, hLe⟩ | ⟨hdim, hLe⟩
  · have hDm : Dm o c = Pc c - Pc o := by
      unfold Dm; rw [if_pos hdim]
    have hm : (Pc c - Pc o) + Pc o - 2 * ((Pc c - Pc o) * Pc o) = Pc c := by
      have hmul : (Pc c - Pc o) * Pc o = 0 := by
        rw [sub_mul, hLe.1, Pc_idem ho, sub_self]
      rw [hmul, mul_zero, sub_zero, sub_add_cancel]
    rw [hDm, Φ₁, Φ₁, rewrite_frame S Si hSi hb, hm]
  · have hDm : Dm o c = Pc o - Pc c := by
      unfold Dm; rw [if_neg hdim]
    have hm : (Pc o - Pc c) + Pc o - 2 * ((Pc o - Pc c) * Pc o) = Pc c := by
      have hmul : (Pc o - Pc c) * Pc o = Pc o - Pc c := by
        rw [sub_mul, Pc_idem ho, hLe.2]
      rw [hmul, two_mul]
      abel
    rw [hDm, Φ₁, Φ₁, rewrite_frame S Si hSi hb, hm]
