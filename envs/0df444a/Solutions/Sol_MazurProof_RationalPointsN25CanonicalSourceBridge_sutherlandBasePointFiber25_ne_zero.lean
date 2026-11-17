-- Prove2me | solution 1 for MazurProof.RationalPointsN25CanonicalSourceBridge.sutherlandBasePointFiber25_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:00.798919+00:00
-- url     : https://prove2.me/submissions/65eb2f4d-2c89-4596-914f-b5b1169b21e3

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25CanonicalSourceBridge
import Definitions.Def_TateOrder25Factor

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandBasePointFiber` and their helpers. -/

namespace MazurProof.RationalPointsN25CanonicalSourceBridge

open RationalPointsN25CanonicalPoints

open RationalPointsN25QuotientAction

open RationalPointsN25SutherlandBridge

open TateOrder25Factor

/-- The integral base-point fibre polynomial is monic. -/
theorem sutherlandBasePointFiberPoly25_monic :
    sutherlandBasePointFiberPoly25.Monic := by
  unfold sutherlandBasePointFiberPoly25
  monicity!

/-- The base-point fibre polynomial has no root modulo two. -/
theorem sutherlandBasePointFiberPoly25_no_root_mod2 (z : ZMod 2) :
    Polynomial.aeval z sutherlandBasePointFiberPoly25 ≠ 0 := by
  simp only [sutherlandBasePointFiberPoly25, map_add, map_sub, map_mul, map_pow, map_ofNat]
  simp only [Polynomial.aeval_X]
  fin_cases z <;> decide

/-- Consequently the base-point fibre polynomial has no rational root.  A
rational root of a monic integral polynomial would be integral, and reduction
of that integer modulo two contradicts the preceding exhaustive check. -/
theorem _root_.solution (y : ℚ) :
    sutherlandBasePointFiber25 y ≠ 0 := by
  intro hy
  have hroot : Polynomial.aeval y sutherlandBasePointFiberPoly25 = 0 := by
    norm_num [sutherlandBasePointFiberPoly25, sutherlandBasePointFiber25,
      Polynomial.aeval_def]
    exact hy
  obtain ⟨z, hz, _⟩ :=
    exists_integer_of_is_root_of_monic
      sutherlandBasePointFiberPoly25_monic hroot
  have hint : Polynomial.aeval z sutherlandBasePointFiberPoly25 = 0 := by
    have h :
        Polynomial.aeval (algebraMap ℤ ℚ z)
            sutherlandBasePointFiberPoly25 = 0 := hz ▸ hroot
    rw [Polynomial.aeval_algebraMap_apply] at h
    exact (IsFractionRing.injective ℤ ℚ)
      (h.trans (map_zero (algebraMap ℤ ℚ)).symm)
  have hmod :
      Polynomial.aeval (algebraMap ℤ (ZMod 2) z)
          sutherlandBasePointFiberPoly25 = 0 := by
    rw [Polynomial.aeval_algebraMap_apply, hint, map_zero]
  exact sutherlandBasePointFiberPoly25_no_root_mod2 _ hmod

end MazurProof.RationalPointsN25CanonicalSourceBridge
