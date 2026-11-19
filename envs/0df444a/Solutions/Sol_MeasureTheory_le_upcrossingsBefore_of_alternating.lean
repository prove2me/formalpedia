-- Prove2me | solution 1 for MeasureTheory.le_upcrossingsBefore_of_alternating
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:10:06.837739+00:00
-- url     : https://prove2.me/submissions/8fb04b1e-05a4-49da-a775-5da64c0f8a1e

import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F001

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}



theorem _root_.solution (hab : a < b) {m : ℕ} {c : ℕ → ℕ}
    (hmono : ∀ i, i + 1 < 2 * m → c i < c (i + 1)) (hN : ∀ i < 2 * m, c i < N)
    (ha : ∀ i < m, f (c (2 * i)) ω ≤ a) (hb : ∀ i < m, b ≤ f (c (2 * i + 1)) ω) :
    m ≤ upcrossingsBefore a b f N ω := by
  have key : ∀ k, k ≤ m →
      k ≤ upcrossingsBefore a b f (if k = 0 then 0 else c (2 * k - 1) + 1) ω := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hprev : (if k = 0 then 0 else c (2 * k - 1) + 1) ≤ c (2 * k) := by
        split_ifs with h0
        · exact Nat.zero_le _
        · have := hmono (2 * k - 1) (by omega)
          rw [show 2 * k - 1 + 1 = 2 * k by omega] at this
          omega
      have h12 : c (2 * k) ≤ c (2 * k + 1) := (hmono (2 * k) (by omega)).le
      have hlt := upcrossingsBefore_lt_of_exists_upcrossing' (f := f) (ω := ω) hab hprev
        (ha k (by omega)) h12 (hb k (by omega))
      rw [if_neg (Nat.succ_ne_zero k), show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      omega
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; exact Nat.zero_le _
  · have h1 := key m le_rfl
    rw [if_neg (by omega)] at h1
    have hle : c (2 * m - 1) + 1 ≤ N := hN (2 * m - 1) (by omega)
    exact h1.trans (upcrossingsBefore_mono hab hle ω)

