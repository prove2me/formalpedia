-- Prove2me | solution 1 for GlobalTheory.SingleBlock.index_blockPar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:37.947683+00:00
-- url     : https://prove2.me/submissions/4c66c657-4ba5-4c62-a9f4-6b0fbd35dc53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Theorems.Thm_GlobalTheory_SingleBlock_card_blockPar
import Theorems.Thm_GlobalTheory_SingleBlock_card_GL_real
import Theorems.Thm_GlobalTheory_SingleBlock_card_GL_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace GlobalTheory.SingleBlock
variable {k : Type} [Field k] {r t : ℕ}
private theorem mul_inv_eq_of_mul_eq_mul {I A a b c P P' : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hP : P ≠ 0) (h : I * (A * (b * (c * P))) = a * b * b * c * (P * P')) :
    I * (A * a⁻¹ * b⁻¹) = P' := by
  have key : I * A = a * b * P' := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hb hc) hP)
    linear_combination h
  calc I * (A * a⁻¹ * b⁻¹) = (I * A) * (a⁻¹ * b⁻¹) := by ring
    _ = P' * (a * a⁻¹) * (b * b⁻¹) := by rw [key]; ring
    _ = P' := by rw [mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, mul_one, mul_one]
end GlobalTheory.SingleBlock
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.SingleBlock
variable {k : Type} [Field k] {r t : ℕ}
namespace GlobalTheory.SingleBlock
theorem _root_.solution [Finite k] (Q : Subgroup (GL (Fin r) k)) :
    ((blockPar t Q).index : ℝ) * ((Nat.card Q : ℝ) * ((Nat.card k : ℝ) ^ (r ^ 2))⁻¹ *
      ((Nat.card k : ℝ) ^ (r * t))⁻¹) =
      ∏ i ∈ Finset.Ioc t (r + t), (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hq : (0 : ℝ) < Nat.card k := Nat.cast_pos.mpr (by omega)
  have hq' : (1 : ℝ) < Nat.card k := by exact_mod_cast hq1
  have hpos : ∀ m : ℕ, 0 < ∏ i ∈ Finset.Ioc 0 m, (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
    intro m
    apply Finset.prod_pos
    intro i hi
    have hi0 : i ≠ 0 := by
      simp only [Finset.mem_Ioc] at hi
      omega
    have : ((Nat.card k : ℝ) ^ i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq' hi0)
    linarith
  have hidx := (blockPar t Q).index_mul_card
  rw [card_blockPar, card_GL_sum] at hidx
  have hR : ((blockPar t Q).index : ℝ) * ((Nat.card Q : ℝ) * ((Nat.card k : ℝ) ^ (r * t) *
      (Nat.card (GL (Fin t) k) : ℝ))) = (Nat.card (GL (Fin (r + t)) k) : ℝ) := by
    exact_mod_cast hidx
  rw [card_GL_real, card_GL_real,
    ← Finset.prod_Ioc_consecutive _ (Nat.zero_le t) (Nat.le_add_left t r)] at hR
  have he : (Nat.card k : ℝ) ^ ((r + t) * (r + t)) = (Nat.card k : ℝ) ^ (r ^ 2) *
      (Nat.card k : ℝ) ^ (r * t) * (Nat.card k : ℝ) ^ (r * t) * (Nat.card k : ℝ) ^ (t * t) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [he] at hR
  exact mul_inv_eq_of_mul_eq_mul (pow_pos hq _).ne' (pow_pos hq _).ne' (pow_pos hq _).ne' (hpos t).ne' hR
end GlobalTheory.SingleBlock
