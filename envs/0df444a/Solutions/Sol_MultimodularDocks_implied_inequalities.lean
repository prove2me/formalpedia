-- Prove2me | solution 1 for MultimodularDocks.implied_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:20:05.551842+00:00
-- url     : https://prove2.me/submissions/b09d96ce-e2a9-4e70-a0ec-f7500f9d3dd2

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular

open MultimodularDocks in
theorem solution (f : ℤ → ℤ → ℝ) :
    (∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
      (f (d + 1) b - f d b ≤ f (d + 1) (b + 1) - f d (b + 1) ↔
        f d (b + 1) - f d b ≤ f (d + 1) (b + 1) - f (d + 1) b)) ∧
    ((∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f d (b + 1) - f d b ≤ f (d + 1) (b + 1) - f (d + 1) b) →
      (∀ d b : ℤ, 1 ≤ d → 1 ≤ b →
        f d b - f d (b - 1) ≤ f (d - 1) (b + 1) - f (d - 1) b) →
      ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f d (b + 1) - f d b ≤ f d (b + 2) - f d (b + 1)) ∧
    ((∀ d b : ℤ, 1 ≤ d → 1 ≤ b →
        f d b - f (d - 1) b ≤ f (d + 1) (b - 1) - f d (b - 1)) →
      (∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f (d + 1) b - f d b ≤ f (d + 1) (b + 1) - f d (b + 1)) →
      ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f (d + 1) b - f d b ≤ f (d + 2) b - f (d + 1) b) ∧
    (IsMultimodular f → ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
      f (d + 1) b - f d b ≤ f (d + 2) b - f (d + 1) b ∧
        f d (b + 1) - f d b ≤ f d (b + 2) - f d (b + 1) ∧
        f (d + 1) b - f d b ≤ f (d + 1) (b + 1) - f d (b + 1)) := by
  have P1 : ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
      (f (d + 1) b - f d b ≤ f (d + 1) (b + 1) - f d (b + 1) ↔
        f d (b + 1) - f d b ≤ f (d + 1) (b + 1) - f (d + 1) b) := by
    intro d b _ _
    constructor <;> intro h <;> linarith
  have P2 : (∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f d (b + 1) - f d b ≤ f (d + 1) (b + 1) - f (d + 1) b) →
      (∀ d b : ℤ, 1 ≤ d → 1 ≤ b →
        f d b - f d (b - 1) ≤ f (d - 1) (b + 1) - f (d - 1) b) →
      ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f d (b + 1) - f d b ≤ f d (b + 2) - f d (b + 1) := by
    intro h1 h2 d b hd hb
    have a := h1 d b hd hb
    have c := h2 (d + 1) (b + 1) (by omega) (by omega)
    rw [show d + 1 - 1 = d by ring, show b + 1 - 1 = b by ring,
      show b + 1 + 1 = b + 2 by ring] at c
    linarith
  have P3 : (∀ d b : ℤ, 1 ≤ d → 1 ≤ b →
        f d b - f (d - 1) b ≤ f (d + 1) (b - 1) - f d (b - 1)) →
      (∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f (d + 1) b - f d b ≤ f (d + 1) (b + 1) - f d (b + 1)) →
      ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f (d + 1) b - f d b ≤ f (d + 2) b - f (d + 1) b := by
    intro h3 h1 d b hd hb
    have a := h1 d b hd hb
    have c := h3 (d + 1) (b + 1) (by omega) (by omega)
    rw [show d + 1 - 1 = d by ring, show b + 1 - 1 = b by ring,
      show d + 1 + 1 = d + 2 by ring] at c
    linarith
  refine ⟨P1, P2, P3, ?_⟩
  intro hM d b hd hb
  obtain ⟨m1, m2, m3⟩ := hM
  have m1' : ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
      f (d + 1) b - f d b ≤ f (d + 1) (b + 1) - f d (b + 1) :=
    fun d b hd hb => (P1 d b hd hb).mpr (m1 d b hd hb)
  exact ⟨P3 m3 m1' d b hd hb, P2 m1 m2 d b hd hb, m1' d b hd hb⟩
