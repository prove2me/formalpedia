-- Prove2me | solution 1 for GoldbergTarjan.Generic.push_or_relabel_applicable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:40:06.295424+00:00
-- url     : https://prove2.me/submissions/972ed187-c2eb-4830-a0a0-b913590e8c96

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Operations

open GoldbergTarjan.Generic

variable {V : Type} [Fintype V] [DecidableEq V]

/-- In `ℕ∞`, `a < b + 1` implies `a ≤ b`. -/
private theorem enat_le_of_lt_succ {a b : ℕ∞} (h : a < b + 1) : a ≤ b := by
  rcases eq_or_ne b ⊤ with hb | hb
  · rw [hb]; exact le_top
  · exact (ENat.lt_add_one_iff hb).mp h

/-- In `ℕ∞`, a finite value is strictly below its successor. -/
private theorem enat_lt_succ {a : ℕ∞} (ha : a ≠ ⊤) : a < a + 1 :=
  (ENat.add_one_le_iff ha).mp (le_refl _)

/-- No self-loops in the residual graph. -/
private theorem residual_self (N : Network V) (f : V → V → ℝ) (hf : IsPreflow N f) (v : V) :
    residualCap N f v v = 0 := by
  have h1 : f v v = -f v v := hf.2.1 v v
  have h2 : f v v = 0 := by linarith
  rw [residualCap, N.cap_self, h2, sub_zero]

/-- Lemma 2.1: some basic operation applies to an active vertex. -/
private theorem push_or_relabel (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V)
    (hf : IsPreflow N f) (hd : IsValidLabeling N f d) (hv : IsActive N f d v) :
    (∃ w, PushApplicable N f d v w) ∨ RelabelApplicable N f d v := by
  by_cases hex : ∃ w, 0 < residualCap N f v w ∧ d v = d w + 1
  · obtain ⟨w, hw1, hw2⟩ := hex
    exact Or.inl ⟨w, hv, hw1, hw2⟩
  · refine Or.inr ⟨hv, fun w hw => ?_⟩
    have h1 : d v ≤ d w + 1 := hd.2.2 v w hw
    have h2 : d v ≠ d w + 1 := fun hc => hex ⟨w, hw, hc⟩
    exact enat_le_of_lt_succ (lt_of_le_of_ne h1 h2)


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V)
    (hf : IsPreflow N f) (hd : IsValidLabeling N f d) (hv : IsActive N f d v) :
    (∃ w, PushApplicable N f d v w) ∨ RelabelApplicable N f d v :=
  push_or_relabel N f d v hf hd hv
