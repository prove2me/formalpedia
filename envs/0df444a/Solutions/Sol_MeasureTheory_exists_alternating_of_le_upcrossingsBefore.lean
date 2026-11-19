-- Prove2me | solution 1 for MeasureTheory.exists_alternating_of_le_upcrossingsBefore
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:18:02.9007+00:00
-- url     : https://prove2.me/submissions/4ea40136-523f-46ba-9520-771565c97be8

import Mathlib.Probability.Martingale.Upcrossing

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}



theorem _root_.solution (hab : a < b) {m : ℕ}
    (hm : m ≤ upcrossingsBefore a b f N ω) :
    ∃ c : ℕ → ℕ, (∀ i, i + 1 < 2 * m → c i < c (i + 1)) ∧ (∀ i < 2 * m, c i < N)
      ∧ (∀ i < m, f (c (2 * i)) ω ≤ a) ∧ (∀ i < m, b ≤ f (c (2 * i + 1)) ω) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    rw [upcrossingsBefore_zero] at hm
    refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩ <;> intro i hi <;> omega
  have hU : ∀ k ≤ m, upperCrossingTime a b f N k ω < N := fun k hk =>
    upperCrossingTime_lt_of_le_upcrossingsBefore hNpos hab (hk.trans hm)
  have hL : ∀ k < m, lowerCrossingTime a b f N k ω < N := fun k hk =>
    lowerCrossingTime_le_upperCrossingTime_succ.trans_lt (hU (k + 1) hk)
  let c : ℕ → ℕ := fun i => if i % 2 = 0 then lowerCrossingTime a b f N (i / 2) ω
    else upperCrossingTime a b f N (i / 2 + 1) ω
  have c_even : ∀ k, c (2 * k) = lowerCrossingTime a b f N k ω := by
    intro k
    show (if (2 * k) % 2 = 0 then _ else _) = _
    rw [if_pos (by omega), show 2 * k / 2 = k by omega]
  have c_odd : ∀ k, c (2 * k + 1) = upperCrossingTime a b f N (k + 1) ω := by
    intro k
    show (if (2 * k + 1) % 2 = 0 then _ else _) = _
    rw [if_neg (by omega), show (2 * k + 1) / 2 = k by omega]
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [c_even, c_odd]
      exact lowerCrossingTime_lt_upperCrossingTime hab (hU (k + 1) (by omega)).ne
    · rw [c_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, c_even]
      exact upperCrossingTime_lt_lowerCrossingTime hab (hL (k + 1) (by omega)).ne
  · intro i hi
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [c_even]; exact hL k (by omega)
    · rw [c_odd]; exact hU (k + 1) (by omega)
  · intro i hi
    rw [c_even]
    have := stoppedValue_lowerCrossingTime (f := f) (a := a) (b := b) (N := N) (n := i) (ω := ω)
      (hL i hi).ne
    simp only [stoppedValue] at this
    exact this
  · intro i hi
    rw [c_odd]
    have := stoppedValue_upperCrossingTime (f := f) (a := a) (b := b) (N := N) (n := i) (ω := ω)
      (hU (i + 1) hi).ne
    simp only [stoppedValue] at this
    exact this

