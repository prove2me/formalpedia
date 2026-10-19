-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Descent.uniform_drop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:55:51.032212+00:00
-- url     : https://prove2.me/submissions/7c34274e-c5cc-47f5-9742-70b00deb10ff

import Mathlib

open Set Function

theorem solution {X : Type*} [TopologicalSpace X] [CompactSpace X] {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f)
    (hdec : ∀ x, f (D x) ≤ f x) (a b : ℝ)
    (hstrict : ∀ x, a ≤ f x → f x ≤ b → f (D x) < f x) :
    ∃ N : ℕ, ∀ x, f x ≤ b → f (D^[N] x) < a := by
  set K : Set X := {x | a ≤ f x ∧ f x ≤ b}
  have hKc : IsCompact K :=
    ((isClosed_le continuous_const hf).inter (isClosed_le hf continuous_const)).isCompact
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨0, fun x hx => ?_⟩
    simp only [iterate_zero, id_eq]
    by_contra h
    have : x ∈ K := ⟨not_lt.1 h, hx⟩
    rw [hK] at this; exact this
  obtain ⟨y, hyK, hy⟩ := hKc.exists_isMinOn hK
    ((hf.sub (hf.comp hD)).continuousOn)
  set δ := f y - f (D y) with hδ
  have hδpos : 0 < δ := by have := hstrict y hyK.1 hyK.2; rw [hδ]; linarith
  have hmin : ∀ x ∈ K, δ ≤ f x - f (D x) := fun x hx => hy hx
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N, fun x hx => ?_⟩
  have key : ∀ k : ℕ, f (D^[k] x) < a ∨ f (D^[k] x) ≤ b - k * δ := by
    intro k
    induction k with
    | zero => right; simpa using hx
    | succ k ih =>
      rw [iterate_succ_apply']
      rcases ih with h | h
      · left; exact lt_of_le_of_lt (hdec _) h
      · by_cases ha : f (D^[k] x) < a
        · left; exact lt_of_le_of_lt (hdec _) ha
        · right
          have hk : (0 : ℝ) ≤ k * δ := by positivity
          have hmem : D^[k] x ∈ K := ⟨not_lt.1 ha, by linarith⟩
          have := hmin _ hmem
          push_cast; linarith
  rcases key N with h | h
  · exact h
  · have : b - a < N * δ := by rwa [div_lt_iff₀ hδpos] at hN
    linarith
