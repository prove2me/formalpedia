-- Prove2me | solution 1 for Groundwork.Colouring.cheb_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:47.256426+00:00
-- url     : https://prove2.me/submissions/5134db2e-15d4-4f6f-a736-3a2bdf0e4267

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Semifield
import Definitions.Def_Groundwork_Net_Colouring
import Theorems.Thm_Groundwork_Colouring_cheb

set_option autoImplicit false
section
open Finset
open Groundwork Groundwork.Colouring
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
local notation "N" => (Fintype.card κ ^ Fintype.card ι)
namespace Groundwork.Colouring
theorem _root_.solution {Ω : Type*} [Fintype Ω] (Y : Ω → ℕ) (A m V t s : ℕ)
    (S1 : (∑ χ, Y χ) * A = Fintype.card Ω * m)
    (S2 : (∑ χ, Y χ ^ 2) * A ^ 2 ≤ Fintype.card Ω * m ^ 2 + V) :
    #{χ : Ω | t * m + s ≤ t * (A * Y χ)} * s ^ 2 ≤ t ^ 2 * V := by
  have hc := cheb (fun χ : Ω => (t : ℤ) * ((A : ℤ) * Y χ - m)) s (by positivity)
  have hsub : #{χ : Ω | t * m + s ≤ t * (A * Y χ)}
      ≤ #{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y χ - m)} := by
    refine card_le_card fun χ h => ?_
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    zify at h
    linarith
  have key : ∀ B : ℕ, B ≤ #{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y χ - m)} →
      B * s ^ 2 ≤ t ^ 2 * V := by
    intro B hB
    have hB' : (B : ℤ) ≤ (#{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y χ - m)} : ℤ) :=
      Nat.cast_le.2 hB
    zify at S1 S2
    have hsum : ∑ χ : Ω, ((t : ℤ) * ((A : ℤ) * Y χ - m)) ^ 2
        = (t : ℤ) ^ 2 * ((∑ χ : Ω, (Y χ : ℤ) ^ 2) * A ^ 2
          - 2 * m * ((∑ χ : Ω, (Y χ : ℤ)) * A) + (Fintype.card Ω : ℤ) * m ^ 2) := by
      have : ∀ χ : Ω, ((t : ℤ) * ((A : ℤ) * Y χ - m)) ^ 2
          = (t : ℤ) ^ 2 * ((Y χ : ℤ) ^ 2 * A ^ 2 - 2 * m * ((Y χ : ℤ) * A) + (m : ℤ) ^ 2) := by
        intro χ; ring
      simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const,
        card_univ, nsmul_eq_mul]
    rw [hsum, S1] at hc
    have a1 : (B : ℤ) * (s : ℤ) ^ 2
        ≤ (#{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y χ - m)} : ℤ) * (s : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_right hB' (sq_nonneg _)
    have a2 : (t : ℤ) ^ 2 * ((∑ χ : Ω, (Y χ : ℤ) ^ 2) * A ^ 2
          - 2 * m * ((Fintype.card Ω : ℤ) * m) + (Fintype.card Ω : ℤ) * m ^ 2)
        ≤ (t : ℤ) ^ 2 * V :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    have a3 : (B : ℤ) * (s : ℤ) ^ 2 ≤ (t : ℤ) ^ 2 * V := a1.trans (hc.trans a2)
    exact_mod_cast a3
  exact key _ hsub
end Groundwork.Colouring
