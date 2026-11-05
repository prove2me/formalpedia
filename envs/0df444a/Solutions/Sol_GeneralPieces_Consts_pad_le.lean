-- Prove2me | solution 1 for GeneralPieces.Consts.pad_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:53.686204+00:00
-- url     : https://prove2.me/submissions/18a6ff3f-5f27-4091-a64f-053ef7f07885

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_GeneralPieces_Half_Consts

set_option autoImplicit false
section
section
open GeneralPieces
open Finset Real ClauseBound.Inst.Half
open GeneralPieces.Consts
namespace GeneralPieces.Consts
theorem _root_.solution {c₀ c₂ lam h D : ℕ} (hl : 1 ≤ lam) (hh : h ≤ c₀ * lam ^ 2) (hD : D ≤ 2 ^ (c₂ * lam)) :
    2 ^ 10 * (h + 2) ^ 4 * (D + 1) ^ 2 ≤ 2 ^ ((4 * c₀ + 2 * c₂ + 28) * lam) := by
  have h2 : lam ^ 2 ≤ 2 ^ (2 * lam) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
  have h3 : 1 ≤ lam ^ 2 := Nat.one_le_pow _ _ hl
  have h1 : h + 2 ≤ 2 ^ (c₀ + 2 + 2 * lam) :=
    calc h + 2 ≤ (c₀ + 2) * lam ^ 2 := by nlinarith
      _ ≤ 2 ^ (c₀ + 2) * 2 ^ (2 * lam) := Nat.mul_le_mul Nat.lt_two_pow_self.le h2
      _ = 2 ^ (c₀ + 2 + 2 * lam) := (pow_add _ _ _).symm
  have hD1 : D + 1 ≤ 2 ^ (c₂ * lam + 1) := by
    have : 1 ≤ 2 ^ (c₂ * lam) := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have h4 : c₀ ≤ c₀ * lam := Nat.le_mul_of_pos_right _ hl
  calc 2 ^ 10 * (h + 2) ^ 4 * (D + 1) ^ 2 ≤ 2 ^ 10 * (2 ^ (c₀ + 2 + 2 * lam)) ^ 4 * (2 ^ (c₂ * lam + 1)) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 4)) (Nat.pow_le_pow_left hD1 2)
    _ = 2 ^ (10 + (c₀ + 2 + 2 * lam) * 4 + (c₂ * lam + 1) * 2) := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ 2 ^ ((4 * c₀ + 2 * c₂ + 28) * lam) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
end GeneralPieces.Consts
