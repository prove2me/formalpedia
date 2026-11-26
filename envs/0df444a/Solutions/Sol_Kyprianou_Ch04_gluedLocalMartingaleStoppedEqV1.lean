-- Prove2me | solution 1 for Kyprianou.Ch04.gluedLocalMartingaleStoppedEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:15:40.914805+00:00
-- url     : https://prove2.me/submissions/bbfc39dd-aa20-4aac-938e-ce72d41cb17a

import Mathlib
open MeasureTheory Filter
open scoped NNReal Classical
set_option autoImplicit false

/-- Consistency on bounded stopped intervals identifies the glued process there. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℕ → NNReal → Ω → ℝ) (τ : ℕ → Ω → NNReal)
    (hτ : ∀ᵐ w ∂P, Monotone (fun n => τ n w))
    (hM : ∀ᵐ w ∂P, ∀ n m : ℕ, n ≤ m → ∀ t,
      M m (min t (τ n w)) w = M n (min t (τ n w)) w) :
    ∀ᵐ w ∂P, ∀ n t,
      (if h : ∃ k : ℕ, min t (τ n w) ≤ τ k w then
        M (Nat.find h) (min t (τ n w)) w else 0) =
      M n (min t (τ n w)) w := by
  filter_upwards [hτ,hM] with w hm hc
  intro n t
  let u := min t (τ n w)
  have h : ∃ k : ℕ, u ≤ τ k w := ⟨n,min_le_right _ _⟩
  rw [dif_pos h]
  have hk := Nat.find_spec h
  have hkn : Nat.find h ≤ n := Nat.find_min' h (min_le_right _ _)
  have he := hc (Nat.find h) n hkn u
  rw [min_eq_left hk] at he
  exact he.symm
