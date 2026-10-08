-- Prove2me | solution 1 for ManneJobShop.Formulation.pair_either_or_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:15:07.142974+00:00
-- url     : https://prove2.me/submissions/621f6580-fb9d-406c-a281-4478035dd83a

import Mathlib



namespace ManneJobShop.Formulation

theorem pe_core (T aj ak xj xk : ℤ) (hT : |xj - xk| ≤ T) :
    (∃ y : ℤ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (xj - xk) ≥ ak ∧ (T + aj) * (1 - y) + (xk - xj) ≥ aj) ↔
      (xj - xk ≥ ak ∨ xk - xj ≥ aj) := by
  have h1 := (abs_le.mp hT)
  constructor
  · rintro ⟨y, ⟨h0, h1'⟩, h3, h4⟩
    have : y = 0 ∨ y = 1 := by omega
    rcases this with rfl | rfl
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · exact ⟨0, ⟨le_rfl, by norm_num⟩, by linarith, by linarith⟩
    · exact ⟨1, ⟨by norm_num, le_rfl⟩, by linarith, by linarith⟩

theorem es_core (T aj ak x : ℤ) (haj : 0 < aj) (hak : 0 < ak) :
    ¬ ∃ y : ℤ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (x - x) ≥ ak ∧ (T + aj) * (1 - y) + (x - x) ≥ aj := by
  rintro ⟨y, ⟨h0, h1⟩, h3, h4⟩
  have : y = 0 ∨ y = 1 := by omega
  rcases this with rfl | rfl <;> simp at h3 h4 <;> omega

end ManneJobShop.Formulation

open ManneJobShop.Formulation


theorem solution (T aj ak xj xk : ℤ) (hT : |xj - xk| ≤ T) :
    (∃ y : ℤ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (xj - xk) ≥ ak ∧ (T + aj) * (1 - y) + (xk - xj) ≥ aj) ↔
      (xj - xk ≥ ak ∨ xk - xj ≥ aj) := by
  exact pe_core T aj ak xj xk hT
