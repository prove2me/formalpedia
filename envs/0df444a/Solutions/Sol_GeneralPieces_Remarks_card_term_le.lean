-- Prove2me | solution 1 for GeneralPieces.Remarks.card_term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:47.143403+00:00
-- url     : https://prove2.me/submissions/8274d132-b85b-41fe-b528-8fed6ec79071

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Num_Remarks

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Remarks
open Finset Levels.Gen ClauseBound.Gen AppRunningTime
namespace GeneralPieces.Remarks
theorem _root_.solution (a c lam B I C₂ : ℕ) (ha : 2 ≤ a) (hlam : 1 ≤ lam) (hI : I ≤ (2 * lam) ^ c) :
    (2 * I + 2) * 2 ^ (c * lam) ≤ (a ^ 2 * (lam + B)) ^ (c + 1) * (2 ^ (c * lam) * (a ^ 2 * (lam + B)) ^ C₂) := by
  have h4 : 4 ≤ a ^ 2 := by nlinarith
  have hX : 4 * lam ≤ a ^ 2 * (lam + B) := Nat.mul_le_mul h4 (by omega)
  obtain ⟨X, hXd⟩ : ∃ X, X = a ^ 2 * (lam + B) := ⟨_, rfl⟩
  rw [← hXd] at hX ⊢
  have h1 : (2 * lam) ^ c ≤ X ^ c := Nat.pow_le_pow_left (by omega) c
  have h2 : 1 ≤ X ^ c := Nat.one_le_pow _ _ (by omega)
  have h3 : 2 * I + 2 ≤ X ^ (c + 1) := by
    calc 2 * I + 2 ≤ 4 * X ^ c := by omega
      _ ≤ X * X ^ c := Nat.mul_le_mul_right _ (by omega)
      _ = X ^ (c + 1) := by ring
  have h5 : 1 ≤ X ^ C₂ := Nat.one_le_pow _ _ (by omega)
  calc (2 * I + 2) * 2 ^ (c * lam) ≤ X ^ (c + 1) * (2 ^ (c * lam) * 1) := by rw [mul_one]; exact Nat.mul_le_mul_right _ h3
    _ ≤ X ^ (c + 1) * (2 ^ (c * lam) * X ^ C₂) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h5)
end GeneralPieces.Remarks
