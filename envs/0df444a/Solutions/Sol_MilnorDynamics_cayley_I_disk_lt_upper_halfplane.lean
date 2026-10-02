-- Prove2me | solution 1 for MilnorDynamics.cayley_I_disk_lt_upper_halfplane
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T14:46:15.000529+00:00
-- url     : https://prove2.me/submissions/40f88ea3-6a88-4beb-aa06-5933f7a0747e

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

-- Proof of `MilnorDynamics.cayley_I_disk_lt_upper_halfplane`
-- (`43792ee7-7ad7-4c72-8da4-d9eb1d6a8d3a`).
--
-- Claim: for `|z| < 1`, `0 < (I * ((z + 1) / (1 - z))).im`. Equivalently the twisted
-- Cayley map `w z = I * (z + 1) / (1 - z)` sends the open unit disc into the UPPER
-- half-plane.
--
-- Structure of the proof:
--
--   `Complex.I_mul_im (z : C) : (I * z).im = z.re`  (Mathlib/Data/Complex/Basic.lean:273)
-- reduces the goal to `0 < ((z + 1) / (1 - z)).re`, which is exactly the Proved
-- sibling `cayley_disk_lt_halfplane` (`a5dd6f7c`).  Because a `Proved` platform
-- theorem is not importable by bare name (see PROVED_NOT_IMPORTABLE.md), that
-- real-part argument is re-derived here in full, verbatim from the accepted source of
-- `a5dd6f7c` (candidate 5419, sha256 92aa12e58ac58fd4).
--
-- `Complex.I_mul_im` carries no `@[simp]` tag, so it is applied with an explicit `rw`
-- rather than left to `simp`.

open scoped OnePoint
open Filter Set
open Complex
open MilnorDynamics

theorem solution (z : ℂ) (hz : z ∈ Metric.ball 0 1) :
    0 < (I * ((z + 1) / (1 - z))).im := by
  -- The rotation lemma: `im (I * w) = re w`. This is the entire content of the target.
  rw [Complex.I_mul_im]
  have hnorm : ‖z‖ < 1 := by simpa using hz
  -- `1 - z ≠ 0`. `sub_eq_zero : a - b = 0 ↔ a = b`, so `sub_eq_zero.mp hc` is `1 = z`,
  -- and the goal is `z = 1`, hence `.symm`.
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro hc
    have hz1 : z = (1 : ℂ) := (sub_eq_zero.mp hc).symm
    rw [hz1, norm_one] at hnorm
    exact (by norm_num : ¬ ((1 : ℝ) < 1)) hnorm
  have hden : ((1 : ℂ) - z) ≠ 0 := hne
  -- `‖z‖ < 1` in a linear ordered ring, so `nlinarith` legitimately closes this.
  have hnn : 0 ≤ ‖z‖ := norm_nonneg z
  have hnum : 0 < (1 : ℝ) - ‖z‖ ^ 2 := by nlinarith
  have hdenpos : 0 < Complex.normSq ((1 : ℂ) - z) := Complex.normSq_pos.mpr hden
  rw [Complex.div_re]
  -- Make all four projections real so the remaining goal is arithmetic over ℝ.
  rw [show ((1 : ℂ) - z).re = 1 - z.re by simp]
  rw [show ((1 : ℂ) - z).im = -z.im by simp]
  rw [show (z + 1).re = z.re + 1 by simp]
  rw [show (z + 1).im = z.im by simp]
  -- `Complex.normSq_eq_norm_sq` turns the denominator into a real norm square, so its
  -- positivity comes from `sq_pos_of_ne_zero`, which needs a NONZERO NORM rather than
  -- a nonzero complex number (`norm_ne_zero_iff.mpr` is the bridge).
  have hnormne : ‖((1 : ℂ) - z)‖ ≠ 0 := norm_ne_zero_iff.mpr hden
  have hdenR : 0 < ‖((1 : ℂ) - z)‖ ^ 2 := sq_pos_of_ne_zero hnormne
  rw [Complex.normSq_eq_norm_sq]
  -- The two summands share the denominator `D = ‖1 - z‖^2`; combine them by `ring`
  -- (certain over ℝ) instead of hunting for a division-combining lemma.
  have hA : (z.re + 1) * (1 - z.re) + z.im * -z.im = (1 : ℝ) - ‖z‖ ^ 2 := by
    linarith [Complex.sq_norm_sub_sq_re z]
  have hD : (0 : ℝ) < ‖((1 : ℂ) - z)‖ ^ 2 := hdenR
  have hsum : (0 : ℝ) < ((z.re + 1) * (1 - z.re) + z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 :=
    div_pos (by linarith [hA, hnum]) hD
  have heq : ((z.re + 1) * (1 - z.re)) / ‖((1 : ℂ) - z)‖ ^ 2 +
      (z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 =
      ((z.re + 1) * (1 - z.re) + z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 := by
    ring
  rw [heq]
  exact hsum
