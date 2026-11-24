-- Prove2me | solution 1 for GlobalTheory.SingleBlock.card_GL_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:41.174798+00:00
-- url     : https://prove2.me/submissions/ed2fa8b6-3af2-4711-9532-595c8142f307

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.SingleBlock
variable {k : Type} [Field k] {r t : ℕ}
namespace GlobalTheory.SingleBlock
theorem _root_.solution [Finite k] (n : ℕ) :
    (Nat.card (GL (Fin n) k) : ℝ) = (Nat.card k : ℝ) ^ (n * n) *
      ∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
  classical
  have := Fintype.ofFinite k
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hq : (0 : ℝ) < Nat.card k := Nat.cast_pos.mpr (by omega)
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => ((Nat.card k ^ n - Nat.card k ^ i : ℕ) : ℝ)) n]
  have step : ∀ i ∈ Finset.range n, ((Nat.card k ^ n - Nat.card k ^ i : ℕ) : ℝ) =
      (Nat.card k : ℝ) ^ n * (1 - ((Nat.card k : ℝ) ^ (n - i))⁻¹) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) hin.le)]
    push_cast
    have hsplit : (Nat.card k : ℝ) ^ n = (Nat.card k : ℝ) ^ i * (Nat.card k : ℝ) ^ (n - i) := by
      rw [← pow_add]
      congr 1
      omega
    have h2 : (Nat.card k : ℝ) ^ n * ((Nat.card k : ℝ) ^ (n - i))⁻¹ = (Nat.card k : ℝ) ^ i := by
      rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq.ne'), mul_one]
    rw [mul_sub, mul_one, h2]
  rw [Finset.prod_congr rfl step, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul]
  congr 1
  apply Finset.prod_nbij' (fun i => n - i) (fun i => n - i)
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_Ioc] at ha
    omega
  · intro a _
    rfl
end GlobalTheory.SingleBlock
