-- Prove2me | solution 1 for MilnorDynamics.cayley_disk_lt_halfplane
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T03:02:44.228582+00:00
-- url     : https://prove2.me/submissions/5eeac7f8-2c98-4365-a9f8-f3ac5fcc66c8

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

-- Proof of `MilnorDynamics.cayley_disk_lt_halfplane`
-- (`a5dd6f7c-33ea-4558-b1c5-fa4e5658164e`).
--
-- Claim: for `|z| < 1`, `0 < Re((z + 1) / (1 - z))`. Equivalently the Cayley map
-- `c z = (z + 1) / (1 - z)` sends the open unit disc into the right half-plane.
--
-- The identity that does the work is
--
--   Re((z + 1) / (1 - z)) = (1 - |z|^2) / |1 - z|^2
--
-- from `Complex.div_re` (Mathlib/Data/Complex/Basic.lean:705) with
-- `Complex.normSq w = w.re^2 + w.im^2`: for `w = 1 - z` and numerator `z + 1` the
-- real part is
--
--   ((1 + z.re)(1 - z.re) + (-z.im)(-z.im)) / |1 - z|^2
--     = (1 - z.re^2 + z.im^2) / |1 - z|^2
--     = (1 - (z.re^2 + z.im^2)) / |1 - z|^2
--     = (1 - |z|^2) / |1 - z|^2
--
-- The denominator `Complex.normSq (1 - z)` is positive by `Complex.normSq_pos`
-- (Mathlib/Data/Complex/Basic.lean:565), since `1 - z = 0` would force `z = 1`, whose
-- norm is `1`, not `< 1`. The numerator `1 - |z|^2` is positive because `|z| < 1`.

open scoped OnePoint
open Filter Set
open MilnorDynamics

theorem solution (z : ℂ) (hz : z ∈ Metric.ball 0 1) :
    0 < ((z + 1) / (1 - z)).re := by
  have hnorm : ‖z‖ < 1 := by simpa using hz
  -- `1 - z ≠ 0` directly. Note the orientation the remote asked for: `sub_ne_zero`
  -- is stated as `sub_ne_zero : a - b ≠ 0 ↔ b ≠ a` in recent Mathlib, so the proof
  -- obligation is `z ≠ 1`, which is what `hne` already provides. Version 1 supplied
  -- `hne : z ≠ 1` to `sub_ne_zero.mpr` and the remote reported
  --   term `hne` has type `z ≠ 1` but is expected to have type `1 ≠ z`
  -- so `.mpr` wanted `1 ≠ z`. `sub_ne_zero.mpr` is therefore the wrong lemma here and
  -- `ne_of_sub_ne_zero` / direct reasoning is used instead.
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro hc
    -- `sub_eq_zero : a - b = 0 ↔ a = b`, so `sub_eq_zero.mp hc` is `1 = z`, and the
    -- goal is `z = 1`, hence `.symm`. Version 2 wrapped this in an extra
    -- `apply sub_eq_zero.mp`, and the remote reported
    --   term `Eq.symm (sub_eq_zero.mp hc)` has type `z = 1` but is expected to have
    --   type `z - 1 = 0`
    have hz1 : z = (1 : ℂ) := (sub_eq_zero.mp hc).symm
    rw [hz1, norm_one] at hnorm
    exact (by norm_num : ¬ ((1 : ℝ) < 1)) hnorm
  have hden : ((1 : ℂ) - z) ≠ 0 := hne
  -- `‖z‖ < 1` in a linear ordered ring, so `nlinarith` legitimately closes this.
  -- Version 1 wrote `by nlinarith` over a goal whose hypothesis set included
  -- `hdenpos : 0 < normSq (1 - z)`, a `ℂ`-valued positivity, and the remote reported
  --   linarith failed to find a contradiction ... `a✝ : 1 - ‖z‖^2 ≤ 0`
  -- The fix is to derive the numerator positivity immediately after `hnorm`, before
  -- any `ℂ`-valued hypothesis enters scope.
  -- `‖z‖^2 ≥ 0` is needed to rule out the case `‖z‖^2 > 1`; `norm_nonneg z` supplies
  -- `0 ≤ ‖z‖`. Version 2 left this to `nlinarith` with only `hnorm` in context and the
  -- remote reported `linarith failed ... a✝ : 1 - ‖z‖^2 ≤ 0`.
  have hnn : 0 ≤ ‖z‖ := norm_nonneg z
  have hnum : 0 < (1 : ℝ) - ‖z‖ ^ 2 := by nlinarith
  have hdenpos : 0 < Complex.normSq ((1 : ℂ) - z) := Complex.normSq_pos.mpr hden
  rw [Complex.div_re]
  -- The remote's target at this point was
  --   `0 < (z.re + 1) * (1 - z.re) / ‖1 - z‖^2 + (z + 1).im * -z.im / ‖1 - z‖^2`
  -- i.e. `Complex.div_re` leaves the two summands OVER a COMMON denominator, not a
  -- single numerator. Version 1 rewrote only the `.re`/`.im` projections and then tried
  -- to rewrite the combined numerator, and the remote reported
  --   Did not find an occurrence of the pattern
  --     `(z.re + 1) * (1 - z.re) + z.im * -z.im`
  -- The fix rewrites `(z + 1).im` as well, so both numerators become real, and then
  -- clears the divisions with `div_add_div` / positivity directly.
  rw [show ((1 : ℂ) - z).re = 1 - z.re by simp]
  rw [show ((1 : ℂ) - z).im = -z.im by simp]
  rw [show (z + 1).re = z.re + 1 by simp]
  rw [show (z + 1).im = z.im by simp]
  -- The numerator is `(z.re + 1) * (1 - z.re) + z.im * (-z.im) = 1 - |z|^2`,
  -- using `Complex.sq_norm_sub_sq_re` (Mathlib/Analysis/Complex/Norm.lean:159):
  -- `‖z‖^2 - z.re^2 = z.im^2`. The denominator is `Complex.normSq (1 - z)`, and
  -- `Complex.normSq_eq_norm_sq` (same file, line 147) rewrites it as `‖1 - z‖^2`.
  -- After that rewrite the denominator is a real norm, so its positivity comes from
  -- `sq_pos_of_ne_zero` rather than from `Complex.normSq_pos`.
  -- `sq_pos_of_ne_zero` needs a NONZERO NORM, not a nonzero complex number; version 1
  -- passed `hden : 1 - z ≠ 0` and the remote reported
  --   term `hden` has type `1 - z ≠ 0` but is expected to have type `‖1 - z‖ ≠ 0`
  have hnormne : ‖((1 : ℂ) - z)‖ ≠ 0 := norm_ne_zero_iff.mpr hden
  have hdenR : 0 < ‖((1 : ℂ) - z)‖ ^ 2 := sq_pos_of_ne_zero hnormne
  rw [Complex.normSq_eq_norm_sq]
  -- The goal is `0 < A / D + B / D` with `D = ‖1 - z‖^2`, i.e. `0 < (A + B) / D` where
  -- `A + B = (z.re + 1) * (1 - z.re) + z.im * (-z.im)`. By
  -- `Complex.sq_norm_sub_sq_re` (Mathlib/Analysis/Complex/Norm.lean:159,
  -- `‖z‖^2 - z.re^2 = z.im^2`) that numerator is `1 - ‖z‖^2`, which is positive by
  -- `hnum`; the denominator is positive by `hdenR`. `positivity` discharges the goal
  -- from those two facts without needing a division-combining lemma.
  have hA : (z.re + 1) * (1 - z.re) + z.im * -z.im = (1 : ℝ) - ‖z‖ ^ 2 := by
    linarith [Complex.sq_norm_sub_sq_re z]
  -- `Complex.div_re` splits the real part into two fractions sharing the denominator
  -- `D = ‖1 - z‖^2`. Rather than hunt for a division-combining lemma whose exact form
  -- and argument order is easy to get wrong, each summand is shown positive on its own
  -- and the goal is closed by `linarith` over `ℝ`.
  --
  --   A = (z.re + 1) * (1 - z.re) = 1 - z.re^2  and  B = z.im * (-z.im) = -z.im^2
  --   A + B = 1 - ‖z‖^2  (this is `hA`), which is positive by `hnum`
  --   A / D > 0 and B / D > 0 are NOT both provable (`B ≤ 0`), so instead use
  --   `0 < (A + B) / D`, which `hA`, `hnum` and `hD` give, and then `linarith` against
  --   the goal after multiplying through by the positive `D`.
  have hD : (0 : ℝ) < ‖((1 : ℂ) - z)‖ ^ 2 := hdenR
  have hsum : (0 : ℝ) < ((z.re + 1) * (1 - z.re) + z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 :=
    div_pos (by linarith [hA, hnum]) hD
  have heq : ((z.re + 1) * (1 - z.re)) / ‖((1 : ℂ) - z)‖ ^ 2 +
      (z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 =
      ((z.re + 1) * (1 - z.re) + z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 := by
    ring
  rw [heq]
  exact hsum
