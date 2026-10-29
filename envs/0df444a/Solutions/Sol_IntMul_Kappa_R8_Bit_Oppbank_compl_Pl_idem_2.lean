-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.compl_Pl_idem
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:14:35.220049+00:00
-- url     : https://prove2.me/submissions/50416a58-a3ab-4bc4-a455-32f1e2cad361

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Aux_PlRankA

open IntMul.Kappa.R8.Bit.Oppbank.Pnd Matrix
open scoped Kronecker

theorem card3_data : ∀ b < 1771,
    ((Finset.univ : Finset (Fin 23)).filter (fun p => (triL b).testBit p.val = true)).card = 3 := by
  decide +kernel

theorem sum_tv {b : ℕ} (hb : b < 1771) : ∑ p : Fin 23, tvQ b p = 3 := by
  simp only [tvQ]
  rw [Finset.sum_boole, card3_data b hb]
  norm_num

theorem tv01 (b : ℕ) (k : Fin 23) : tvQ b k = 0 ∨ tvQ b k = 1 := by
  unfold tvQ
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem yx {b : ℕ} (hb : b < 1771) : ∑ k, yv b k * xv b k = 1 := by
  have key : ∀ k, yv b k * xv b k = tvQ b k / 3 := by
    intro k
    simp only [yv, xv]
    rw [sum_tv hb]
    rcases tv01 b k with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_div, sum_tv hb]
  norm_num

theorem Pl_idem {b : ℕ} (hb : b < 1771) : Pl b * Pl b = Pl b := by
  ext i j
  simp only [Pl, mul_apply, vecMulVec_apply]
  have : ∑ k, xv b i * yv b k * (xv b k * yv b j) =
      xv b i * yv b j * ∑ k, yv b k * xv b k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [this, yx hb, mul_one]

theorem compl_idem {b : ℕ} (hb : b < 1771) : (1 - Pl b) * (1 - Pl b) = 1 - Pl b := by
  rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Pl_idem hb]
  abel

theorem trace_Pl {b : ℕ} (hb : b < 1771) : (Pl b).trace = 1 := by
  rw [← yx hb]
  simp only [trace, diag, Pl, vecMulVec_apply]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem rank_idem {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℚ) (h : P * P = P) :
    (P.rank : ℚ) = P.trace := by
  have hf : IsIdempotentElem (Matrix.toLin' P) := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have := ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hf).trace
  rw [Matrix.trace_toLin'_eq] at this
  rw [this]
  rfl

theorem Pl_rank {b : ℕ} (hb : b < 1771) : (Pl b).rank = 1 := by
  have := rank_idem _ (Pl_idem hb)
  rw [trace_Pl hb] at this
  exact_mod_cast this

theorem compl_rank {b : ℕ} (hb : b < 1771) : (1 - Pl b).rank = 22 := by
  have := rank_idem _ (compl_idem hb)
  rw [trace_sub, trace_one, trace_Pl hb] at this
  norm_num at this
  exact_mod_cast this

theorem K_rank (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) (A B : M23) (hA : A * A = A) (hB : B * B = B) :
    (K S Si A B).rank = A.rank * B.rank := by
  have hX : (A ⊗ₖ B) * (A ⊗ₖ B) = A ⊗ₖ B := by rw [← mul_kronecker_mul, hA, hB]
  have hK : K S Si A B * K S Si A B = K S Si A B := by
    simp only [K, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Si S, hSi, Matrix.one_mul, ← Matrix.mul_assoc (A ⊗ₖ B), hX]
  have h1 := rank_idem _ hK
  have htr : (K S Si A B).trace = A.trace * B.trace := by
    simp only [K]
    rw [trace_mul_comm, ← Matrix.mul_assoc, hSi, Matrix.one_mul, trace_kronecker]
  rw [htr, ← rank_idem _ hA, ← rank_idem _ hB] at h1
  exact_mod_cast h1

end Aux_PlRankA

open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R8.Bit.Oppbank.Pnd Matrix in
theorem solution {b : ℕ} (hb : b < v) : (1 - Pl b) * (1 - Pl b) = 1 - Pl b :=
  Aux_PlRankA.compl_idem hb
