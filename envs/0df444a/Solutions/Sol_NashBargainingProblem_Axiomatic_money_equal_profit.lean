-- Prove2me | solution 1 for NashBargainingProblem.Axiomatic.money_equal_profit
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:21.801313+00:00
-- url     : https://prove2.me/submissions/b9f559b6-6e3c-4b40-a03f-3f2d9c7defa7

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NashWork

theorem money_equal_profit (m : ℝ) (hm : 0 < m) (S : Set (ℝ × ℝ))
    (hS : {u ∈ S | 0 ≤ u.1 ∧ 0 ≤ u.2} = {u : ℝ × ℝ | 0 ≤ u.1 ∧ 0 ≤ u.2 ∧ u.1 + u.2 ≤ m})
    (p : ℝ × ℝ) :
    (p ∈ S ∧ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
      ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2) ↔
    p = (m / 2, m / 2) := by
  have hmem : ∀ u : ℝ × ℝ, (u ∈ S ∧ 0 ≤ u.1 ∧ 0 ≤ u.2) ↔ (0 ≤ u.1 ∧ 0 ≤ u.2 ∧ u.1 + u.2 ≤ m) := by
    intro u
    exact Set.ext_iff.1 hS u
  constructor
  · rintro ⟨hpS, hp1, hp2, hmax⟩
    have hp := (hmem p).1 ⟨hpS, hp1, hp2⟩
    by_contra hne
    have hmid := (hmem (m / 2, m / 2)).2 ⟨by simp; positivity, by simp; positivity, by simp⟩
    have := hmax _ hmid.1 hmid.2.1 hmid.2.2 (fun h => hne h.symm)
    simp only at this
    nlinarith [sq_nonneg (p.1 - p.2), hp.2.2]
  · rintro rfl
    have hmid := (hmem (m / 2, m / 2)).2 ⟨by simp; positivity, by simp; positivity, by simp⟩
    refine ⟨hmid.1, hmid.2.1, hmid.2.2, ?_⟩
    intro s hs h1 h2 hne
    have hs' := (hmem s).1 ⟨hs, h1, h2⟩
    simp only
    by_contra hge
    push Not at hge
    apply hne
    have h3 : s.1 + s.2 ≤ m := hs'.2.2
    have h4 : s.1 = s.2 := by nlinarith [sq_nonneg (s.1 - s.2), sq_nonneg (s.1 + s.2 - m)]
    have h5 : s.1 = m / 2 := by nlinarith [sq_nonneg (s.1 - s.2), sq_nonneg (s.1 + s.2 - m)]
    exact Prod.ext h5 (h4 ▸ h5)

end NashWork

theorem solution (m : ℝ) (hm : 0 < m) (S : Set (ℝ × ℝ))
    (hS : {u ∈ S | 0 ≤ u.1 ∧ 0 ≤ u.2} = {u : ℝ × ℝ | 0 ≤ u.1 ∧ 0 ≤ u.2 ∧ u.1 + u.2 ≤ m})
    (p : ℝ × ℝ) :
    (p ∈ S ∧ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
      ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2) ↔
    p = (m / 2, m / 2) :=
  NashWork.money_equal_profit m hm S hS p

#print axioms solution
