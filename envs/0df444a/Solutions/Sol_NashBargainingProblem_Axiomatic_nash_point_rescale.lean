-- Prove2me | solution 1 for NashBargainingProblem.Axiomatic.nash_point_rescale
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:08.256992+00:00
-- url     : https://prove2.me/submissions/d8a9617a-c93d-490f-a125-acf7d446d031

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NashWork

theorem nash_point_rescale (S : Set (ℝ × ℝ)) (p : ℝ × ℝ)
    (hp_mem : p ∈ S) (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2)
    (hp_max : ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2)
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    let S' := (fun u : ℝ × ℝ => (α₁ * u.1, α₂ * u.2)) '' S
    let p' : ℝ × ℝ := (α₁ * p.1, α₂ * p.2)
    p' ∈ S' ∧ 0 ≤ p'.1 ∧ 0 ≤ p'.2 ∧
      ∀ s ∈ S', 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p' → s.1 * s.2 < p'.1 * p'.2 := by
  intro S' p'
  refine ⟨⟨p, hp_mem, rfl⟩, mul_nonneg hα₁.le hp1, mul_nonneg hα₂.le hp2, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ h1 h2 hne
  have hu1 : 0 ≤ u.1 := nonneg_of_mul_nonneg_right (by simpa using h1) hα₁
  have hu2 : 0 ≤ u.2 := nonneg_of_mul_nonneg_right (by simpa using h2) hα₂
  have hup : u ≠ p := fun h => hne (by rw [h])
  have := hp_max u hu hu1 hu2 hup
  have hpos : 0 < α₁ * α₂ := mul_pos hα₁ hα₂
  show α₁ * u.1 * (α₂ * u.2) < α₁ * p.1 * (α₂ * p.2)
  nlinarith

end NashWork

theorem solution (S : Set (ℝ × ℝ)) (p : ℝ × ℝ)
    (hp_mem : p ∈ S) (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2)
    (hp_max : ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2)
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    let S' := (fun u : ℝ × ℝ => (α₁ * u.1, α₂ * u.2)) '' S
    let p' : ℝ × ℝ := (α₁ * p.1, α₂ * p.2)
    p' ∈ S' ∧ 0 ≤ p'.1 ∧ 0 ≤ p'.2 ∧
      ∀ s ∈ S', 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p' → s.1 * s.2 < p'.1 * p'.2 :=
  NashWork.nash_point_rescale S p hp_mem hp1 hp2 hp_max α₁ α₂ hα₁ hα₂

#print axioms solution
