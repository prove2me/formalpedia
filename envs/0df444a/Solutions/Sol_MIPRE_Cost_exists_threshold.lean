-- Prove2me | solution 1 for MIPRE.Cost.exists_threshold
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:31:14.745371+00:00
-- url     : https://prove2.me/submissions/c889433d-24c8-4c59-bd6e-a0ac16135363

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Growth.lean (solution of MIPRE.Cost.exists_threshold);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Theorems.Thm_MIPRE_Cost_mul_pow_le_two_pow

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost
open Polynomial
/-- A polynomial over `ℕ` is bounded by its coefficient sum times the top power. -/
theorem polynomial_eval_le_sum_coeff_mul_pow (Q : Polynomial ℕ) {y : ℕ} (hy : 1 ≤ y) :
    Q.eval y ≤ (∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i) * y ^ Q.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hy (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution (Q : Polynomial ℕ) :
    ∃ K : ℕ, ∀ x n : ℕ, 2 ^ (K + 1 + x) ≤ n → Q.eval (x + Nat.size n) ≤ n + 1 := by
  obtain ⟨D, hD⟩ : ∃ D, D = Q.natDegree := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i := ⟨_, rfl⟩
  have hQ : ∀ y, 1 ≤ y → Q.eval y ≤ A * y ^ D := fun y hy => by
    rw [hA, hD]; exact polynomial_eval_le_sum_coeff_mul_pow Q hy
  refine ⟨2 * A * 2 ^ D * (D + 1) ^ (D + 1), fun x n hn => ?_⟩
  have hlt : 2 * A * 2 ^ D * (D + 1) ^ (D + 1) + 1 + x < Nat.size n := Nat.lt_size.mpr hn
  have hn' : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
  have h1 : Q.eval (x + Nat.size n) ≤ Q.eval (2 * Nat.size n) :=
    polynomial_eval_mono Q (by omega)
  have h2 : Q.eval (2 * Nat.size n) ≤ A * (2 * Nat.size n) ^ D := hQ _ (by omega)
  have h3 : 2 * (A * 2 ^ D * Nat.size n ^ D) ≤ 2 ^ Nat.size n := by
    have := mul_pow_le_two_pow (2 * A * 2 ^ D) D (Nat.size n) (by omega)
    calc 2 * (A * 2 ^ D * Nat.size n ^ D) = 2 * A * 2 ^ D * Nat.size n ^ D := by ring
      _ ≤ 2 ^ Nat.size n := this
  have h4 : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h4] at h3
  calc Q.eval (x + Nat.size n) ≤ Q.eval (2 * Nat.size n) := h1
    _ ≤ A * (2 * Nat.size n) ^ D := h2
    _ = A * 2 ^ D * Nat.size n ^ D := by rw [mul_pow, mul_assoc]
    _ ≤ 2 ^ (Nat.size n - 1) := by omega
    _ ≤ n := hn'
    _ ≤ n + 1 := Nat.le_succ n
