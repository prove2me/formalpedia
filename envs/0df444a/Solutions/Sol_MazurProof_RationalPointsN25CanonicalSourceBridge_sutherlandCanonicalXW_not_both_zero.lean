-- Prove2me | solution 1 for MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandCanonicalXW_not_both_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:02.841941+00:00
-- url     : https://prove2.me/submissions/278b01a4-7c1d-46b4-9bb0-0479a2d20beb

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25CanonicalSourceBridge
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_sutherlandBasePointFiber25_ne_zero

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandBasePointFiber` and their helpers. -/

namespace MazurProof.RationalPointsN25CanonicalSourceBridge

open RationalPointsN25CanonicalPoints

open RationalPointsN25QuotientAction

open RationalPointsN25SutherlandBridge

open TateOrder25Factor

/-- Exact Bezout identity for the first and fourth adjoint cores.  It is the
kernel-checked resultant certificate used to exclude affine base points. -/
theorem sutherlandBasePoint_bezout_identity25 (x y : ℚ) :
    sutherlandBasePointBezoutX25 x y * sutherlandCanonicalXCore25 x y +
        sutherlandBasePointBezoutW25 x y * sutherlandCanonicalWCore25 x y =
      (y - 1) ^ 7 * sutherlandBasePointFiber25 y := by
  simp only [sutherlandBasePointBezoutX25, sutherlandCanonicalXCore25,
    sutherlandBasePointBezoutW25, sutherlandCanonicalWCore25,
    sutherlandBasePointFiber25]
  ring

/-- On the affine chart `y≠1`, the first and fourth canonical coordinates
cannot vanish simultaneously.  The first coordinate exposes its adjoint core;
the fourth either exposes its core or forces `x=y-1`, and both branches are
excluded by exact polynomial identities. -/
theorem _root_.solution
    {x y : ℚ} (hy1 : y ≠ 1) :
    sutherlandCanonicalX25 x y ≠ 0 ∨ sutherlandCanonicalW25 x y ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hX, hW⟩
  have hySub : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
  have hXcore : sutherlandCanonicalXCore25 x y = 0 := by
    have hmul : (y - 1) ^ 2 * sutherlandCanonicalXCore25 x y = 0 := by
      rw [sutherlandCanonicalX25] at hX
      simpa only [neg_mul, neg_eq_zero] using hX
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hySub)
  have hWcases : x - y + 1 = 0 ∨ sutherlandCanonicalWCore25 x y = 0 := by
    have hWmul : (x - y + 1) * sutherlandCanonicalWCore25 x y = 0 := by
      simpa [sutherlandCanonicalW25] using hW
    exact mul_eq_zero.mp hWmul
  rcases hWcases with hlinear | hWcore
  · have hx : x = y - 1 := by linarith
    have hspecial :
        sutherlandCanonicalXCore25 (y - 1) y = (y - 1) ^ 5 := by
      simp only [sutherlandCanonicalXCore25]
      ring
    rw [hx] at hXcore
    rw [hspecial] at hXcore
    exact hySub ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hXcore)
  · have hbezout := sutherlandBasePoint_bezout_identity25 x y
    rw [hXcore, hWcore, mul_zero, mul_zero, zero_add] at hbezout
    have hfiber : sutherlandBasePointFiber25 y = 0 :=
      (mul_eq_zero.mp hbezout.symm).resolve_left (pow_ne_zero 7 hySub)
    exact sutherlandBasePointFiber25_ne_zero y hfiber

end MazurProof.RationalPointsN25CanonicalSourceBridge
