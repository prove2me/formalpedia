-- Prove2me | solution 1 for Helfgott.slow_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T20:55:21.684576+00:00
-- url     : https://prove2.me/submissions/74d27a73-013a-4a0d-8235-cf9b2e5f1cf6

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-!
A sharp version of the slowly degrading Cauchy–Schwarz estimate used in
H. A. Helfgott, arXiv:1312.7748v2, Lemma 4.1 and (4.5). Polarization gives
constant 1/2 in place of 2.71, without the small-distance hypothesis.
Written by Codex.
-/

open scoped InnerProductSpace

namespace Helfgott

theorem slow_cauchy_schwarz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) :
    |⟪v, w⟫_ℝ - ‖v‖ * ‖w‖| ≤ (1 / 2 : ℝ) * ‖v - w‖ ^ 2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (real_inner_le_norm v w))]
  nlinarith [norm_sub_sq_real v w, sq_nonneg (‖v‖ - ‖w‖)]

theorem equal_norm_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) (h : ‖w‖ = ‖v‖) :
    ⟪v, w⟫_ℝ = ‖v‖ ^ 2 - (1 / 2 : ℝ) * ‖v - w‖ ^ 2 := by
  have hp := norm_sub_sq_real v w
  rw [h] at hp
  linarith

end Helfgott

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) :
    |⟪v, w⟫_ℝ - ‖v‖ * ‖w‖| ≤ (1 / 2 : ℝ) * ‖v - w‖ ^ 2 :=
  Helfgott.slow_cauchy_schwarz v w

#print axioms solution
