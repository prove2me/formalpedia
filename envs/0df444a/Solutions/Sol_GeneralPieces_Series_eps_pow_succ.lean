-- Prove2me | solution 1 for GeneralPieces.Series.eps_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:34:17.362131+00:00
-- url     : https://prove2.me/submissions/9c9a9de7-fada-445b-b134-c0ef70defe0a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Definitions.Def_GeneralPieces_Series_Rings
import Theorems.Thm_GeneralPieces_Series_ext_cf
import Theorems.Thm_GeneralPieces_Series_cf_zero
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_diag
import Theorems.Thm_GeneralPieces_Series_cf_sub_mul
import Theorems.Thm_GeneralPieces_Series_sub_mul_eps
attribute [local simp] GeneralPieces.Series.cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (N : ℕ) : eps ^ (N + 1) = diag (-(N : ℤ) - 1) (fun j => ((j.toNat + N).choose N : ℚ)) 0 := by
  induction N with
  | zero =>
    rw [zero_add, pow_one, eps]
    refine ext_cf fun x y => ?_
    rw [cf_diag, cf_diag]
    simp
  | succ N ih =>
    have key : (mo 1 0 - mo 0 1) * diag (-((N + 1 : ℕ) : ℤ) - 1) (fun j => ((j.toNat + (N + 1)).choose (N + 1) : ℚ)) 0 = eps ^ (N + 1) := by
      rw [ih]
      refine ext_cf fun x y => ?_
      rw [cf_sub_mul, cf_diag, cf_diag, cf_diag]
      by_cases hd : x + y = -(N : ℤ) - 1
      · rcases lt_trichotomy y 0 with hy | hy | hy
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), sub_zero]
        · subst hy
          rw [if_pos ⟨le_refl _, by push_cast; omega⟩, if_neg (by omega), if_pos ⟨le_refl _, hd⟩]
          simp
        · obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = n + 1 := ⟨(y - 1).toNat, by omega⟩
          rw [if_pos ⟨by omega, by push_cast; omega⟩, if_pos ⟨by omega, by push_cast; omega⟩, if_pos ⟨by omega, hd⟩]
          have e1 : ((n : ℤ) + 1).toNat = n + 1 := by omega
          have e2 : ((n : ℤ) + 1 - 1).toNat = n := by omega
          rw [e1, e2, show n + 1 + (N + 1) = (n + 1 + N) + 1 by ring, Nat.choose_succ_succ, show n + 1 + N = n + (N + 1) by ring]
          push_cast
          ring
      · rw [if_neg (fun g => hd (by have := g.2; push_cast at this; omega)), if_neg (fun g => hd (by have := g.2; push_cast at this; omega)),
          if_neg (fun g => hd g.2), sub_zero]
    calc eps ^ (N + 1 + 1) = eps ^ (N + 1) * eps := pow_succ _ _
      _ = ((mo 1 0 - mo 0 1) * eps) * diag (-((N + 1 : ℕ) : ℤ) - 1) (fun j => ((j.toNat + (N + 1)).choose (N + 1) : ℚ)) 0 := by rw [← key]; ring
      _ = _ := by rw [sub_mul_eps, one_mul]
end GeneralPieces.Series
