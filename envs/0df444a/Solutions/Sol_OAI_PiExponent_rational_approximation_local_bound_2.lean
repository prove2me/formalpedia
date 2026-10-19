-- Prove2me | solution 2 for OAI.PiExponent.rational_approximation_local_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T12:32:15.452972+00:00
-- url     : https://prove2.me/submissions/687371aa-921b-4aa3-b5de-9cf8c42c5ce0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_pi_approximation_determinant_sequences
import Theorems.Thm_OAI_PiExponent_asymptotic_determinant_bounds_inconsistent
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q → |(p : ℝ)| ≤ 4 * (q : ℝ) →
        (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
  classical
  by_contra h
  push_neg at h
  have hbad : ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ),
      Q ≤ q ∧ |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu) := by
    intro Q
    obtain ⟨p, q, hq, hp, hclose⟩ := h (max Q 2) (le_max_right Q 2)
    exact ⟨p, q, (le_max_left Q 2).trans hq, hclose.le⟩
  obtain ⟨theta, x, ear, ean, collisionLimit, b, D, err, collision,
      hgap, hcollision, herr, hcol, hb0, hb, hlower, hupper⟩ :=
    OAI.PiExponent.pi_approximation_determinant_sequences nu hnu hbad
  exact OAI.PiExponent.asymptotic_determinant_bounds_inconsistent
    nu theta x ear ean collisionLimit b D err collision
    (by linarith) hgap hcollision herr hcol hb0 hb hlower hupper
