-- Prove2me | solution 1 for Kawahira.classification_by_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:20:11.121415+00:00
-- url     : https://prove2.me/submissions/8a2d8f84-353d-4b0e-a9bf-c0af0e0d7501

import Definitions.Def_Kawahira_zeta

open Complex Topology

theorem solution (lam : ℂ) (h : lam ≠ 1) :
    (‖lam‖ < 1 ↔ 1 / 2 < (1 / (1 - lam)).re) ∧
      (‖lam‖ = 1 ↔ (1 / (1 - lam)).re = 1 / 2) ∧
      (1 < ‖lam‖ ↔ (1 / (1 - lam)).re < 1 / 2) := by
  have hden : 0 < ‖1 - lam‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h.symm))
  have hre : (1 / (1 - lam)).re = (1 - lam.re) / ‖1 - lam‖ ^ 2 := by
    rw [one_div, inv_re]
    simp [Complex.normSq_eq_norm_sq]
  have hnorm : ‖1 - lam‖ ^ 2 = 1 - 2 * lam.re + ‖lam‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq]
    ring
  rw [hre]
  constructor
  · constructor
    · intro hl
      apply (lt_div_iff₀ hden).2
      nlinarith [hnorm, norm_nonneg lam]
    · intro hl
      have := (lt_div_iff₀ hden).1 hl
      nlinarith [hnorm, norm_nonneg lam]
  constructor
  · constructor
    · intro hl
      apply (div_eq_iff hden.ne').2
      nlinarith [hnorm]
    · intro hl
      have := (div_eq_iff hden.ne').1 hl
      nlinarith [hnorm, norm_nonneg lam]
  · constructor
    · intro hl
      apply (div_lt_iff₀ hden).2
      nlinarith [hnorm]
    · intro hl
      have := (div_lt_iff₀ hden).1 hl
      nlinarith [hnorm, norm_nonneg lam]
