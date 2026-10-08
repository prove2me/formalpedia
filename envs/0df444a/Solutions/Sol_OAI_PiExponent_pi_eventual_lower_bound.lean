-- Prove2me | solution 1 for OAI.PiExponent.pi_eventual_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:03:06.41727+00:00
-- url     : https://prove2.me/submissions/15189284-f270-4f09-9af5-5ef49ae63a14
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_pi_approximation_determinant_sequences
import Theorems.Thm_OAI_PiExponent_asymptotic_determinant_bounds_inconsistent

open OAI.PiExponent

theorem solution : PiEventualLowerBound := by
  intro nu hnu
  by_contra h
  push Not at h
  have hbad : ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ),
      Q ≤ q ∧ |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu) := by
    intro Q
    obtain ⟨p, q, hq, herr⟩ := h (max Q 2) (le_max_right _ _)
    exact ⟨p, q, (le_max_left _ _).trans hq, herr.le⟩
  obtain ⟨theta, x, ear, ean, collisionLimit, b, d, err, collision,
    hgap, hcollision, herr, hcol, hb0, hb, hlower, hupper⟩ :=
    pi_approximation_determinant_sequences nu hnu hbad
  exact asymptotic_determinant_bounds_inconsistent
    nu theta x ear ean collisionLimit b d err collision
    (by linarith) hgap hcollision herr hcol hb0 hb hlower hupper
