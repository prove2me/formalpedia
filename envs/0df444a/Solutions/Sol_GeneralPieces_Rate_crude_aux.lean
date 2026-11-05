-- Prove2me | solution 1 for GeneralPieces.Rate.crude_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:15.724547+00:00
-- url     : https://prove2.me/submissions/b2242b3f-0140-4e5c-a957-8a60656b48ca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (k a c lam B L B' : ℕ) (hlam : 1 ≤ lam) (hka : k ≤ a) (ha : 4 ≤ a) (hL : L ≤ a ^ 4 * lam + 1)
    (hB : B' ≤ a ^ 4 * lam + a ^ 2 * (a * B + a ^ 2 * (2 * lam) ^ c)) :
    a * (a ^ 3 * lam + (a * B + a ^ 2 * (2 * lam) ^ c)) ≤ (a ^ 2 * (lam + B)) ^ (c + 4) ∧ k * (L + B') ≤ (a ^ 2 * (lam + B)) ^ (c + 5) := by
  obtain ⟨A, hA⟩ : ∃ A, A = a ^ 2 := ⟨_, rfl⟩
  have haA : a ≤ A := by rw [hA, sq]; exact Nat.le_mul_of_pos_left _ (by omega)
  have e4 : a ^ 4 = A * A := by rw [hA]; ring
  have e3 : a * a ^ 3 = A * A := by rw [hA]; ring
  have e2 : a * a = A := by rw [hA]; ring
  rw [e4] at hL hB
  rw [← hA] at hB ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = A * (lam + B) := ⟨_, rfl⟩
  rw [← hX]
  have hAX : A ≤ X := by rw [hX]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hX5 : 5 ≤ X := by nlinarith
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ c := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have h1 : A * lam ≤ X := by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)
  have h2 : A * B ≤ X := by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)
  have h2l : 2 * lam ≤ X := le_trans (Nat.mul_le_mul_right _ (by omega)) h1
  have ht : (2 * lam) ^ c ≤ Y := by rw [hY]; exact Nat.pow_le_pow_left h2l c
  generalize (2 * lam) ^ c = t at *
  have hN : A * A * lam ≤ X * X * Y := by
    calc A * A * lam = A * (A * lam) * 1 := by ring
      _ ≤ X * X * Y := by gcongr
  have hXX : X ≤ X * X * Y := by
    calc X = 1 * X * 1 := by ring
      _ ≤ X * X * Y := by gcongr; omega
  have hT : A * A * t ≤ X * X * Y := by gcongr
  have p4 : X ^ (c + 4) = X * X * (X * X * Y) := by rw [hY]; ring
  have p5 : X ^ (c + 5) = X * (X * X) * (X * X * Y) := by rw [hY]; ring
  have hXX5 : 5 ≤ X * X := by nlinarith
  constructor
  · rw [p4]
    calc a * (a ^ 3 * lam + (a * B + A * t)) = a * a ^ 3 * lam + (a * a * B + a * A * t) := by ring
      _ = A * A * lam + (A * B + a * A * t) := by rw [e3, e2]
      _ ≤ X * X * Y + (X * X * Y + A * A * t) :=
          Nat.add_le_add hN (Nat.add_le_add (h2.trans hXX) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ haA)))
      _ ≤ X * X * Y + (X * X * Y + X * X * Y) := by omega
      _ = 3 * (X * X * Y) := by ring
      _ ≤ X * X * (X * X * Y) := Nat.mul_le_mul_right _ (by omega)
  · rw [p5]
    have hs : L + B' ≤ 5 * (X * X * Y) := by
      have h3 : A * (a * B + A * t) ≤ 2 * (X * X * Y) := by
        calc A * (a * B + A * t) = a * (A * B) + A * A * t := by ring
          _ ≤ X * X * 1 + X * X * Y := Nat.add_le_add (by rw [mul_one]; exact Nat.mul_le_mul (haA.trans hAX) h2) hT
          _ ≤ X * X * Y + X * X * Y := Nat.add_le_add_right (Nat.mul_le_mul_left _ hY1) _
          _ = 2 * (X * X * Y) := by ring
      have h4 : 1 ≤ X * X * Y := le_trans (by omega) hXX
      omega
    calc k * (L + B') ≤ X * (5 * (X * X * Y)) := Nat.mul_le_mul (hka.trans (haA.trans hAX)) hs
      _ = X * 5 * (X * X * Y) := by ring
      _ ≤ X * (X * X) * (X * X * Y) := by gcongr
end GeneralPieces.Rate
