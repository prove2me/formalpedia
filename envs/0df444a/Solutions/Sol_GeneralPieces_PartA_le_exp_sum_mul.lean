-- Prove2me | solution 1 for GeneralPieces.PartA.le_exp_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:56:58.585684+00:00
-- url     : https://prove2.me/submissions/15dcbf5a-83c1-4fd5-9e1f-f72b0eadd570

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
namespace GeneralPieces.PartA
theorem _root_.solution (u a b : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hu : 0 ≤ u 0)
    (h : ∀ l, u (l + 1) ≤ (1 + a l) * u l + b l) (l : ℕ) :
    u l ≤ Real.exp (∑ j ∈ range l, a j) * (u 0 + ∑ j ∈ range l, b j) := by
  induction l with
  | zero => simp
  | succ l ih =>
    obtain ⟨S, hS⟩ : ∃ S, S = ∑ j ∈ range l, a j := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T, T = u 0 + ∑ j ∈ range l, b j := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := hS ▸ sum_nonneg fun j _ => ha j
    have hT0 : 0 ≤ T := hT ▸ add_nonneg hu (sum_nonneg fun j _ => hb j)
    rw [sum_range_succ, sum_range_succ, ← add_assoc, ← hS, ← hT, Real.exp_add]
    rw [← hS, ← hT] at ih
    have hE : 0 < Real.exp S := Real.exp_pos _
    have h1 : (1 + a l) * u l ≤ (1 + a l) * (Real.exp S * T) :=
      mul_le_mul_of_nonneg_left ih (by linarith [ha l])
    have h2 : (1 + a l) * (Real.exp S * T) ≤ Real.exp (a l) * (Real.exp S * T) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (a l)]) (by positivity)
    have h3 : 1 * b l ≤ Real.exp S * Real.exp (a l) * b l :=
      mul_le_mul_of_nonneg_right
        (one_le_mul_of_one_le_of_one_le (Real.one_le_exp hS0) (Real.one_le_exp (ha l))) (hb l)
    nlinarith [h l]
end GeneralPieces.PartA
