-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_induction_of_extend
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:28:45.95938+00:00
-- url     : https://prove2.me/submissions/d1581257-1da4-46eb-8529-c7b78e8bb1c6

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

theorem solution
    {α : Type}
    (N : Nat)
    (Good : α → Nat → Prop)
    (hbase : ∃ x : α, Good x 0)
    (hstep : ∀ m : Nat, m ≤ N → ∀ x : α, Good x m →
      ∃ y : α, Good y (m + 1)) :
    ∃ x : α, Good x (N + 1) := by
  revert hstep
  induction N with
  | zero =>
      intro hstep
      obtain ⟨x, hx⟩ := hbase
      obtain ⟨y, hy⟩ := hstep 0 (by rfl) x hx
      exact ⟨y, hy⟩
  | succ n ih =>
      intro hstep
      obtain ⟨x, hx⟩ := ih (fun m hm => hstep m (Nat.le_trans hm (Nat.le_succ n)))
      obtain ⟨y, hy⟩ := hstep (n + 1) (by rfl) x hx
      exact ⟨y, by simpa [Nat.succ_eq_add_one] using hy⟩