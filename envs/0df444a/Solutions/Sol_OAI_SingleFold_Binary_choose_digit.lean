-- Prove2me | solution 1 for OAI.SingleFold.Binary.choose_digit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:16:29.974986+00:00
-- url     : https://prove2.me/submissions/f3bb2a7c-a189-4e05-b099-a6d54e953fdd

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

open OAI OAI.SingleFold OAI.SingleFold.Binary
theorem h49_low (B s : ℕ) (f : ℕ → ℕ) (hf : ∀ t < s, f t < B) :
    ∑ t ∈ Finset.range s, f t * B^t < B^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := ih (fun t ht => hf t (by omega))
    have h2 := hf s (by omega)
    have : f s * B^s ≤ (B - 1) * B^s := Nat.mul_le_mul_right _ (by omega)
    have h3 : (B - 1) * B^s + B^s = B^s * B := by
      rcases B with _ | B
      · omega
      · simp only [Nat.add_sub_cancel]; ring
    omega

theorem h49_split (B s m : ℕ) (f : ℕ → ℕ) :
    ∑ t ∈ Finset.range (s+1+m), f t * B^t =
      ∑ t ∈ Finset.range s, f t * B^t +
        B^s * (f s + B * ∑ t ∈ Finset.range m, f (s+1+t) * B^t) := by
  rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.mul_sum, mul_add, Finset.mul_sum]
  have : ∀ t ∈ Finset.range m, f (s+1+t) * B^(s+1+t) = B^s * (B * (f (s+1+t) * B^t)) := by
    intro t _; rw [pow_add, pow_add]; ring
  rw [Finset.sum_congr rfl this]; ring

theorem h49_digit (B s m : ℕ) (f : ℕ → ℕ) (hf : ∀ t ≤ s, f t < B) :
    (∑ t ∈ Finset.range (s+1+m), f t * B^t) / B^s % B = f s := by
  rw [h49_split]
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hf s le_rfl)
  have hl := h49_low B s f (fun t ht => hf t ht.le)
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hl, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf s le_rfl)]

theorem solution {x y B : ℕ} (hxy : x≤y) (hB : 2^y<B) :
    (B+1)^y/B^x%B=y.choose x := by
  have e : (B+1)^y = ∑ t ∈ Finset.range (x+1+(y-x)), y.choose t * B^t := by
    rw [show x+1+(y-x) = y+1 by omega, add_pow]
    apply Finset.sum_congr rfl; intro t _; simp [mul_comm]
  rw [e, h49_digit]
  intro t _
  exact lt_of_le_of_lt (Nat.choose_le_two_pow y t) hB

