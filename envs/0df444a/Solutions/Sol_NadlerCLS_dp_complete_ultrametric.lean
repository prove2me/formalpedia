-- Prove2me | solution 1 for NadlerCLS.dp_complete_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:05:40.254832+00:00
-- url     : https://prove2.me/submissions/c993aa6d-70e2-4cb5-92b8-1b586434db31

import Mathlib
import Definitions.Def_NadlerCLS_dp

set_option autoImplicit false

open Filter Topology

open NadlerCLS in
theorem solution {α : Type*} (p : α → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    (∀ x y, dp p x y = 0 ↔ x = y) ∧
    (∀ x y, dp p x y = dp p y x) ∧
    (∀ x y z, dp p x z ≤ max (dp p x y) (dp p y z)) ∧
    (∀ x y, x ≠ y → 1 ≤ dp p x y ∧ dp p x y ≤ 2) ∧
    (∀ u : ℕ → α, (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, dp p (u a) (u b) < ε) →
      (∃ N : ℕ, ∀ a ≥ N, u a = u N) ∧
      ∃ x, Tendsto (fun a => dp p (u a) x) atTop (𝓝 0)) := by
  classical
  have hne : ∀ x y, x ≠ y → dp p x y = 1 + max (p x) (p y) := by
    intro x y h; unfold dp; simp [h]
  have heq : ∀ x, dp p x x = 0 := by intro x; unfold dp; simp
  have hrange : ∀ x y, x ≠ y → 1 ≤ dp p x y ∧ dp p x y ≤ 2 := by
    intro x y h
    rw [hne x y h]
    have := hp x; have := hp y
    constructor
    · have : 0 ≤ max (p x) (p y) := le_max_of_le_left (hp x).1
      linarith
    · have : max (p x) (p y) ≤ 1 := max_le (hp x).2 (hp y).2
      linarith
  have hzero : ∀ x y, dp p x y = 0 ↔ x = y := by
    intro x y
    constructor
    · intro h
      by_contra hxy
      have := (hrange x y hxy).1
      linarith
    · rintro rfl; exact heq x
  refine ⟨hzero, ?_, ?_, hrange, ?_⟩
  · intro x y
    by_cases h : x = y
    · subst h; rfl
    · rw [hne x y h, hne y x (Ne.symm h), max_comm]
  · intro x y z
    by_cases hxz : x = z
    · subst hxz
      rw [heq]
      exact le_max_of_le_left (by
        by_cases hxy : x = y
        · subst hxy; rw [heq]
        · linarith [(hrange x y hxy).1])
    · rw [hne x z hxz]
      by_cases hxy : x = y
      · subst hxy
        rw [hne x z hxz]; exact le_max_right _ _
      · by_cases hyz : y = z
        · subst hyz; rw [hne x y hxy]; exact le_max_left _ _
        · rw [hne x y hxy, hne y z hyz]
          rcases le_total (p x) (p z) with h | h
          · rw [max_eq_right h]
            exact le_max_of_le_right (by linarith [le_max_right (p y) (p z)])
          · rw [max_eq_left h]
            exact le_max_of_le_left (by linarith [le_max_left (p x) (p y)])
  · intro u hu
    obtain ⟨N, hN⟩ := hu (1 / 2) (by norm_num)
    have hconst : ∀ a ≥ N, u a = u N := by
      intro a ha
      by_contra h
      have h1 := (hrange _ _ h).1
      have h2 := hN a ha N le_rfl
      linarith
    refine ⟨⟨N, hconst⟩, u N, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with a ha
    rw [hconst a ha, heq]
