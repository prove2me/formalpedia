-- Prove2me | solution 1 for NashBargainingProblem.Axiomatic.square_unique_symmetric_undominated
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:13.13598+00:00
-- url     : https://prove2.me/submissions/a87f906d-b039-4a12-a4b7-bc1179766254

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NashWork

theorem square_unique_symmetric_undominated (h : ℝ) (hh : 0 < h) (p : ℝ × ℝ)
    (hp : p ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}) :
    (p.1 = p.2 ∧
      ∀ t ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h},
        ¬ (p.1 < t.1 ∧ p.2 < t.2)) ↔ p = ((1 : ℝ), (1 : ℝ)) := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  constructor
  · rintro ⟨hsym, hund⟩
    have h11 : ((1 : ℝ), (1 : ℝ)) ∈
        {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} :=
      ⟨by simp; linarith, by simp; norm_num, by simp; exact hh.le⟩
    by_contra hne
    have hle : p.1 ≤ 1 := by linarith
    have hlt : p.1 < 1 := lt_of_le_of_ne hle (fun h' => hne (Prod.ext h' (hsym ▸ h')))
    exact hund _ h11 ⟨hlt, by rw [← hsym]; exact hlt⟩
  · rintro rfl
    refine ⟨rfl, fun t ht ⟨h1, h2⟩ => ?_⟩
    obtain ⟨_, ht2, _⟩ := ht
    simp only at h1 h2
    linarith

end NashWork

theorem solution (h : ℝ) (hh : 0 < h) (p : ℝ × ℝ)
    (hp : p ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}) :
    (p.1 = p.2 ∧
      ∀ t ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h},
        ¬ (p.1 < t.1 ∧ p.2 < t.2)) ↔ p = ((1 : ℝ), (1 : ℝ)) :=
  NashWork.square_unique_symmetric_undominated h hh p hp

#print axioms solution
