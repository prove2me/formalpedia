-- Prove2me | solution 1 for OAI.SingleFold.Packed.bits_mask
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:33:02.472992+00:00
-- url     : https://prove2.me/submissions/59adaca8-2f44-4d38-81de-c9005dfcce5e

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

open OAI OAI.SingleFold OAI.SingleFold.Packed
theorem h49_bits_tb (x y : ℕ) : OAI.SingleFold.Packed.Bits x y ↔ ∀ i, x.testBit i=true → y.testBit i=true := by
  unfold OAI.SingleFold.Packed.Bits
  simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  refine forall_congr' (fun i => ?_)
  have h1 := Nat.mod_lt (x/2^i) (show 0 < 2 by norm_num)
  have h2 := Nat.mod_lt (y/2^i) (show 0 < 2 by norm_num)
  omega

theorem h49_ones_tb {w c : ℕ} (hw : 0 < w) (hc : c < 2^w) (k : ℕ) :
    c * OAI.SingleFold.Packed.ones (2^w) k < 2^(w*k) ∧
    ∀ i, (c * OAI.SingleFold.Packed.ones (2^w) k).testBit i = true ↔ (i < w*k ∧ c.testBit (i % w) = true) := by
  induction k with
  | zero =>
    simp [OAI.SingleFold.Packed.ones, OAI.SingleFold.Packed.pack]
  | succ k ih =>
    obtain ⟨hlt, htb⟩ := ih
    have he : c * OAI.SingleFold.Packed.ones (2^w) (k+1) = 2^(w*k) * c + c * OAI.SingleFold.Packed.ones (2^w) k := by
      simp only [OAI.SingleFold.Packed.ones, OAI.SingleFold.Packed.pack, Finset.sum_range_succ]
      rw [← pow_mul]; ring
    rw [he]
    refine ⟨?_, ?_⟩
    · have : 2^(w*(k+1)) = 2^(w*k) * 2^w := by rw [← pow_add]; ring_nf
      rw [this]
      have h1 : 2^(w*k) * c + 2^(w*k) ≤ 2^(w*k) * 2^w := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hc
      omega
    · intro i
      rw [Nat.testBit_two_pow_mul_add _ hlt]
      split_ifs with hi
      · rw [htb i]; constructor
        · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, h2⟩
        · rintro ⟨_, h2⟩; exact ⟨hi, h2⟩
      · push_neg at hi
        have hmod : (i - w*k) % w = i % w := by
          rw [show i = (i - w*k) + w*k by omega, Nat.add_mul_mod_self_left]; congr 1; omega
        by_cases hi2 : i - w*k < w
        · rw [← hmod, Nat.mod_eq_of_lt hi2]
          constructor
          · intro h; exact ⟨by rw [Nat.mul_succ]; omega, h⟩
          · rintro ⟨_, h⟩; exact h
        · push_neg at hi2
          have hf : c.testBit (i - w*k) = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hi2))
          rw [hf]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨h, _⟩; rw [Nat.mul_succ] at h; omega

theorem h49_digit_tb (w x t j : ℕ) :
    (OAI.SingleFold.Packed.digit (2^w) x t).testBit j = (decide (j < w) && x.testBit (j + w*t)) := by
  unfold OAI.SingleFold.Packed.digit
  rw [← pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem solution {w k c x : ℕ} (hw : 0 < w) (hc : c < 2^w) :
    Bits x (c*ones (2^w) k) ↔ x < (2^w)^k ∧ ∀t < k, Bits (digit (2^w) x t) c := by
  obtain ⟨_, hY⟩ := h49_ones_tb hw hc k
  rw [h49_bits_tb]
  simp only [hY, h49_bits_tb, h49_digit_tb, ← pow_mul]
  constructor
  · intro h
    refine ⟨Nat.lt_pow_two_of_testBit x (fun i hi => ?_), fun t ht j hj => ?_⟩
    · by_contra hb
      have := (h i (by simpa using hb)).1; omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      have := (h _ hj.2).2
      rwa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj.1] at this
  · rintro ⟨hx, h⟩ i hi
    have hik : i < w*k := by
      by_contra hc'; push_neg at hc'
      have := Nat.ge_two_pow_of_testBit hi
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc'
      omega
    refine ⟨hik, ?_⟩
    have ht : i / w < k := by rw [Nat.div_lt_iff_lt_mul hw]; linarith [Nat.mul_comm w k]
    have := h (i / w) ht (i % w)
    apply this
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨Nat.mod_lt _ hw, ?_⟩
    rw [Nat.mod_add_div]; exact hi

