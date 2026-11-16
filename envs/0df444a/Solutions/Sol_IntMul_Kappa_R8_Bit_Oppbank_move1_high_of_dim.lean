-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.move1_high_of_dim
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:30:53.401391+00:00
-- url     : https://prove2.me/submissions/9a999f7c-9fde-4f0a-9158-f857466f37d3

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
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
open scoped Kronecker
open Matrix

private theorem Pc_high' : Pc 1 = 1 := by simp [Pc]

private theorem dimCF_one : dimCF 1 = 23 := by simp [dimCF]

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

private theorem Dm_from_high_lt {c : ℕ} (hd : dimCF c < 23) : Dm 1 c = 1 - Pc c := by
  have hdim : ¬ dimCF 1 ≤ dimCF c := by
    rw [dimCF_one]; exact not_le.2 hd
  unfold Dm
  rw [if_neg hdim, Pc_high']

private theorem move_high_same (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (b : ℕ) : pswQ (K S Si (Dm 1 1) (Pl b)) * Φ₁ S Si b 1 = Φ₁ S Si b 1 := by
  have hdim : dimCF 1 ≤ dimCF 1 := le_rfl
  have hDm : Dm 1 1 = 0 := by
    unfold Dm
    rw [if_pos hdim, Pc_high', sub_self]
  have hz : K S Si (0 : M23) (Pl b) = 0 := by
    rw [K, Matrix.zero_kronecker, Matrix.mul_zero, Matrix.zero_mul]
  have hp0 : pswQ (0 : Matrix (Fin 529) (Fin 529) ℚ) = 1 := by
    unfold pswQ
    rw [sub_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  rw [hDm, hz, hp0, Matrix.one_mul]

theorem solution (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) {c b : ℕ} (hc : c < codeBound) (hb : b < 1771)
    (hd : c = 1 ∨ dimCF c < 23) :
    pswQ (K S Si (Dm 1 c) (Pl b)) * Φ₁ S Si b 1 = Φ₁ S Si b c := by
  rcases hd with rfl | hd
  · exact move_high_same S Si b
  · -- `dimCF 1 = 23 ≰ dimCF c`, so `Dm 1 c = 1 - Pc c`.
    rw [Dm_from_high_lt hd, Φ₁, Φ₁, Pc_high', pswQ_mul', K_mul' S Si hSi, Pl_idem' hb,
      K_two_left', ← K_add_left', ← K_sub_left']
    have hm : (1 - Pc c) + (1 : M23) - 2 * ((1 - Pc c) * (1 : M23)) = Pc c := by
      simp only [mul_one, two_mul]
      abel
    rw [hm]
