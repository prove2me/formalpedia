-- Prove2me | solution 1 for GeneralPieces.binomRules
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:26:04.057911+00:00
-- url     : https://prove2.me/submissions/f76eb3b0-3053-4978-8570-9836ab107824

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_GeneralPieces_Ring_binom_natCast
import Theorems.Thm_GeneralPieces_Ring_binom_neg

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces Finset GeneralPieces.Ring
namespace GeneralPieces
theorem _root_.solution : BinomRules where
  pascal := fun k j => by
    rcases lt_trichotomy j (-1) with hj | rfl | hj
    · rw [binom_neg (k + 1) (by omega : j + 1 < 0), binom_neg k (by omega : j < 0), binom_neg k (by omega : j + 1 < 0), add_zero]
    · rw [binom_neg k (by omega : (-1 : ℤ) < 0)]
      have : (-1 : ℤ) + 1 = ((0 : ℕ) : ℤ) := by norm_num
      rw [this, binom_natCast, binom_natCast, Ring.choose_zero_right, Ring.choose_zero_right, zero_add]
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j)
      have : ((i : ℕ) : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [this, binom_natCast, binom_natCast, binom_natCast, Ring.choose_succ_succ]
  vandermonde := fun k k' i => by
    rw [binom_natCast, add_comm k k', Ring.add_choose_eq i (Commute.all k' k), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun j hj => ?_
    have hj' := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have : (i : ℤ) - j = ((i - j : ℕ) : ℤ) := by omega
    rw [this, binom_natCast, binom_natCast, mul_comm]
end GeneralPieces
