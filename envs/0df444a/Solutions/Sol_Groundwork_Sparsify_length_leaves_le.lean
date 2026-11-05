-- Prove2me | solution 1 for Groundwork.Sparsify.length_leaves_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:29.718756+00:00
-- url     : https://prove2.me/submissions/45e50f21-f140-455f-aa4d-5e0244434f33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Definitions.Def_StepMachines_Math_SparsifyTree
import Theorems.Thm_Groundwork_Sparsify_sum_choose_succ
import Theorems.Thm_Groundwork_Sparsify_one_le_sum_choose

set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
variable {step} {G : σ → ℕ → ℕ → Prop} {D T q : ℕ}
namespace Groundwork.Sparsify
theorem _root_.solution (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k d h : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) (hd : D ≤ p + d) (hh : T < t + (h + 1) * q) :
    (leaves step k s).length ≤ ∑ j ∈ range (h + 1), d.choose j := by
  induction k generalizing d h s p t with
  | zero => simpa [leaves] using one_le_sum_choose d h
  | succ k ih =>
    rw [leaves]
    split
    · simpa using one_le_sum_choose d h
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      have hbl := hb _ _ _ hl
      have hbr := hb _ _ _ hr
      obtain _ | d := d
      · omega
      obtain _ | h := h
      · omega
      have h1 := ih d (h + 1) l (p + 1) t hl (by omega) hh
      have h2 := ih d h r (p + 1) (t + q) hr (by omega) (by rw [Nat.add_mul (h + 1) 1 q] at hh; omega)
      rw [List.length_append, sum_choose_succ]
      omega
end Groundwork.Sparsify
