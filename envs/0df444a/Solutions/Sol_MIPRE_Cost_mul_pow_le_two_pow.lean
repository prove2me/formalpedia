-- Prove2me | solution 1 for MIPRE.Cost.mul_pow_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:30:36.660512+00:00
-- url     : https://prove2.me/submissions/005e3ce5-930b-48d6-9982-9cf72eb992e5

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Growth.lean (solution of MIPRE.Cost.mul_pow_le_two_pow);
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

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution (A D σ : ℕ) (h : A * (D + 1) ^ (D + 1) ≤ σ) :
    A * σ ^ D ≤ 2 ^ σ := by
  have hD : 0 < D + 1 := Nat.succ_pos D
  have h1 : A * (D + 1) ^ D ≤ σ / (D + 1) := by
    rw [Nat.le_div_iff_mul_le hD, mul_assoc, ← pow_succ]
    exact h
  have h2 : σ ≤ (D + 1) * (σ / (D + 1) + 1) := (Nat.lt_mul_div_succ σ hD).le
  have h3 : σ / (D + 1) * (D + 1) ≤ σ := Nat.div_mul_le_self σ (D + 1)
  have h4 : σ / (D + 1) + 1 ≤ 2 ^ (σ / (D + 1)) := Nat.lt_two_pow_self
  calc A * σ ^ D ≤ A * ((D + 1) * (σ / (D + 1) + 1)) ^ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 D)
    _ = A * (D + 1) ^ D * (σ / (D + 1) + 1) ^ D := by rw [mul_pow, mul_assoc]
    _ ≤ σ / (D + 1) * (σ / (D + 1) + 1) ^ D := Nat.mul_le_mul_right _ h1
    _ ≤ (σ / (D + 1) + 1) ^ (D + 1) := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _) |>.trans
          (le_of_eq (Nat.mul_comm _ _))
    _ ≤ (2 ^ (σ / (D + 1))) ^ (D + 1) := Nat.pow_le_pow_left h4 _
    _ = 2 ^ (σ / (D + 1) * (D + 1)) := by rw [← pow_mul]
    _ ≤ 2 ^ σ := Nat.pow_le_pow_right (by norm_num) h3
