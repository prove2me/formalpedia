-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:44:33.043705+00:00
-- url     : https://prove2.me/submissions/ea1a64f1-29fa-4bd3-a3bd-b813975241b5

import Mathlib

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (a b : Fin m → ℕ) (hab : a ≠ b) :
    Disjoint
      {x : Fin m → ℝ | ∀ i,
        w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)}
      {x : Fin m → ℝ | ∀ i,
        w i * (b i : ℝ) ≤ x i ∧ x i < w i * ((b i : ℝ) + 1)} := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  apply hab
  funext i
  obtain ⟨h1, h2⟩ := hxa i
  obtain ⟨h3, h4⟩ := hxb i
  have hw' := hw i
  have e1 : (a i : ℝ) < b i + 1 := by
    by_contra h; push Not at h; nlinarith
  have e2 : (b i : ℝ) < a i + 1 := by
    by_contra h; push Not at h; nlinarith
  have e1' : a i < b i + 1 := by exact_mod_cast e1
  have e2' : b i < a i + 1 := by exact_mod_cast e2
  omega
