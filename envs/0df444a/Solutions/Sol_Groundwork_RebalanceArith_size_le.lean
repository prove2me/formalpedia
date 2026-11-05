-- Prove2me | solution 1 for Groundwork.RebalanceArith.size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:48.914409+00:00
-- url     : https://prove2.me/submissions/19427c82-7d1e-4193-b724-163c623edad5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_StepMachines_Math_RebalanceArith
import Theorems.Thm_Groundwork_RebalanceArith_beta_le

set_option autoImplicit false
section
open Groundwork Groundwork.RebalanceArith
namespace Groundwork.RebalanceArith
theorem _root_.solution {K g : ℕ} (A c₁ d : ℕ) (hK : 2 ≤ K) (hKg : K ≤ g) :
    ∃ A' : ℕ, ∀ P B U β B' S S' sc sc' Stot : ℕ, 1 ≤ P → U ≤ g * P → K ^ 3 * β ≤ K ^ 3 + K * U + g * P →
      B' ≤ d * (P + B) → S' ≤ S + c₁ * (sc + P + B) ^ c₁ → sc' ≤ c₁ * (sc + P) →
      Stot ≤ c₁ * (sc + P + B) ^ c₁ + S' + A * (sc' + B' + β) ^ A → Stot ≤ S + A' * (sc + P + B) ^ A' := by
  refine ⟨2 * c₁ + A * (c₁ + (d + 3 * g)) ^ A + A, fun P B U β B' S S' sc sc' Stot hP hU hβ hB' hS' hsc' hS => ?_⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ℕ, A' = 2 * c₁ + A * (c₁ + (d + 3 * g)) ^ A + A := ⟨_, rfl⟩
  rw [← hA']
  have hb := beta_le (by omega) (by omega) hP hU hβ
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = sc + P + B := ⟨_, rfl⟩
  rw [← hZ] at hS' hS ⊢
  have hZ1 : 1 ≤ Z := by omega
  have hbase : sc' + B' + β ≤ (c₁ + (d + 3 * g)) * Z := by
    have e1 : (c₁ + (d + 3 * g)) * Z =
        c₁ * (sc + P) + c₁ * B + d * (P + B) + 3 * (g * P) + 3 * (g * B) + (d + 3 * g) * sc := by
      rw [hZ]; ring
    omega
  have h1 : (sc' + B' + β) ^ A ≤ (c₁ + (d + 3 * g)) ^ A * Z ^ A' :=
    calc (sc' + B' + β) ^ A ≤ ((c₁ + (d + 3 * g)) * Z) ^ A := Nat.pow_le_pow_left hbase A
      _ = (c₁ + (d + 3 * g)) ^ A * Z ^ A := Nat.mul_pow ..
      _ ≤ (c₁ + (d + 3 * g)) ^ A * Z ^ A' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ1 (by omega))
  have h2 : Z ^ c₁ ≤ Z ^ A' := Nat.pow_le_pow_right hZ1 (by omega)
  have h3 : A * (sc' + B' + β) ^ A ≤ A * (c₁ + (d + 3 * g)) ^ A * Z ^ A' := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h1
  have h4 : c₁ * Z ^ c₁ ≤ c₁ * Z ^ A' := Nat.mul_le_mul_left _ h2
  have h5 : A' * Z ^ A' = 2 * (c₁ * Z ^ A') + A * (c₁ + (d + 3 * g)) ^ A * Z ^ A' + A * Z ^ A' := by rw [hA']; ring
  omega
end Groundwork.RebalanceArith
