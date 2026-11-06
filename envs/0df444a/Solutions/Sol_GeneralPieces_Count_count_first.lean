-- Prove2me | solution 1 for GeneralPieces.Count.count_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:40.687923+00:00
-- url     : https://prove2.me/submissions/07d59872-50dc-4939-a05b-a16f7eaec89a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_Remarks
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_GeneralPieces_Rec_Count
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Count
open Levels.Gen ClauseBound.Gen
namespace GeneralPieces.Count
theorem _root_.solution (X T s u a κ q : ℝ) (A G c D₁ C₂ C₃ : ℕ) (hX : 2 ≤ X) (hT : 1 ≤ T) (hs : 1 ≤ s) (hu : 1 ≤ u) (ha : a ≤ X ^ A)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ X ^ G) (hq : q ≤ X ^ (c + 1) * (u * X ^ C₂)) :
    a * ((κ + T * s * (u * X ^ C₂)) * X ^ D₁ + 2 * X ^ C₃) + q + X ^ C₃ ≤ X ^ (A + G + (D₁ + C₂ + C₃ + c + 4)) * T * (s * u) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨W, hW⟩ : ∃ W, W = T * s * u := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by rw [hW]; exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hT hs) hu
  have hW0 : 0 ≤ W := by linarith
  have huW : u ≤ W := by rw [hW]; exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hT hs)
  have pw : ∀ i j : ℕ, i ≤ j → X ^ i ≤ X ^ j := fun i j h => pow_le_pow_right₀ hX1 h
  have e0 : T * s * (u * X ^ C₂) = W * X ^ C₂ := by rw [hW]; ring
  have e1 : X ^ (A + G + (D₁ + C₂ + C₃ + c + 4)) * T * (s * u) = X ^ (A + G + (D₁ + C₂ + C₃ + c + 4)) * W := by rw [hW]; ring
  rw [e0, e1]
  have b1 : κ + W * X ^ C₂ ≤ X ^ (G + C₂ + 1) * W := by
    have c1 : κ ≤ X ^ (G + C₂) * W :=
      calc κ ≤ X ^ G := hκ
        _ ≤ X ^ (G + C₂) := pw _ _ (by omega)
        _ ≤ X ^ (G + C₂) * W := le_mul_of_one_le_right (by positivity) hW1
    have c2 : W * X ^ C₂ ≤ X ^ (G + C₂) * W := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (pw _ _ (by omega)) hW0
    have c3 : 2 * (X ^ (G + C₂) * W) ≤ X * (X ^ (G + C₂) * W) := mul_le_mul_of_nonneg_right hX (by positivity)
    calc κ + W * X ^ C₂ ≤ X * (X ^ (G + C₂) * W) := by linarith
      _ = X ^ (G + C₂ + 1) * W := by ring
  have b2 : (κ + W * X ^ C₂) * X ^ D₁ + 2 * X ^ C₃ ≤ X ^ (G + C₂ + D₁ + C₃ + 2) * W := by
    have c1 : (κ + W * X ^ C₂) * X ^ D₁ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) * W :=
      calc (κ + W * X ^ C₂) * X ^ D₁ ≤ (X ^ (G + C₂ + 1) * W) * X ^ D₁ := mul_le_mul_of_nonneg_right b1 (by positivity)
        _ = X ^ (G + C₂ + 1 + D₁) * W := by ring
        _ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) * W := mul_le_mul_of_nonneg_right (pw _ _ (by omega)) hW0
    have c2 : 2 * X ^ C₃ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) * W :=
      calc 2 * X ^ C₃ ≤ X * X ^ C₃ := mul_le_mul_of_nonneg_right hX (by positivity)
        _ = X ^ (C₃ + 1) := by ring
        _ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) := pw _ _ (by omega)
        _ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) * W := le_mul_of_one_le_right (by positivity) hW1
    have c3 : 2 * (X ^ (G + C₂ + D₁ + C₃ + 1) * W) ≤ X * (X ^ (G + C₂ + D₁ + C₃ + 1) * W) :=
      mul_le_mul_of_nonneg_right hX (by positivity)
    calc (κ + W * X ^ C₂) * X ^ D₁ + 2 * X ^ C₃ ≤ X * (X ^ (G + C₂ + D₁ + C₃ + 1) * W) := by linarith
      _ = X ^ (G + C₂ + D₁ + C₃ + 2) * W := by ring
  obtain ⟨E, hE⟩ : ∃ E, E = A + G + C₂ + D₁ + C₃ + c + 2 := ⟨_, rfl⟩
  have b3 : a * ((κ + W * X ^ C₂) * X ^ D₁ + 2 * X ^ C₃) ≤ X ^ E * W :=
    calc a * ((κ + W * X ^ C₂) * X ^ D₁ + 2 * X ^ C₃) ≤ X ^ A * (X ^ (G + C₂ + D₁ + C₃ + 2) * W) :=
          mul_le_mul ha b2 (by positivity) (by positivity)
      _ = X ^ (A + (G + C₂ + D₁ + C₃ + 2)) * W := by ring
      _ ≤ X ^ E * W := mul_le_mul_of_nonneg_right (pw _ _ (by omega)) hW0
  have b4 : q ≤ X ^ E * W :=
    calc q ≤ X ^ (c + 1) * (u * X ^ C₂) := hq
      _ = X ^ (c + 1 + C₂) * u := by ring
      _ ≤ X ^ E * W := mul_le_mul (pw _ _ (by omega)) huW (by linarith) (by positivity)
  have b5 : X ^ C₃ ≤ X ^ E * W :=
    calc X ^ C₃ ≤ X ^ E := pw _ _ (by omega)
      _ ≤ X ^ E * W := le_mul_of_one_le_right (by positivity) hW1
  have h4 : 3 * (X ^ E * W) ≤ X ^ 2 * (X ^ E * W) := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have e2 : X ^ (A + G + (D₁ + C₂ + C₃ + c + 4)) = X ^ 2 * X ^ E := by rw [← pow_add]; congr 1; omega
  rw [e2]
  linarith
end GeneralPieces.Count
