-- Prove2me | solution 1 for MazurProof.RationalPointsN25SutherlandBridge.tateToSutherland_on_plane
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:39.184183+00:00
-- url     : https://prove2.me/submissions/8b42a844-de73-4f93-a42e-f05548b3cff5

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandS_ne_one_on_raw
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandYDen_ne_zero_on_raw
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawX1Plane25_zero_of_tate
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateR_ne_one
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherlandCommon_ne_zero
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherlandYDen_ne_zero
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandCommon_ne_zero_on_raw
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawToOptimized_bihomogeneous_identity
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherlandY_eq_raw
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateC_ne_zero_of_F25

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandModel` and their helpers. -/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-- On the affine chart `K*B≠0`, the bihomogeneous expression equals
`K⁸B⁸ f(X/K,KD/B)`.  This records exactly which denominators were cleared. -/
theorem sutherlandBihomogenized25_eq_affine (X K D B : ℚ) (hK : K ≠ 0) (hB : B ≠ 0) :
    sutherlandBihomogenized25 X K D B = K ^ 8 * B ^ 8 * sutherlandX1Plane25 (X / K) (K * D / B) := by
  simp only [sutherlandBihomogenized25, sutherlandHomogeneousCoefficientEight, sutherlandHomogeneousCoefficientSeven, sutherlandHomogeneousCoefficientSix, sutherlandHomogeneousCoefficientFive, sutherlandHomogeneousCoefficientFour, sutherlandHomogeneousCoefficientThree, sutherlandHomogeneousCoefficientTwo, sutherlandHomogeneousCoefficientOne, sutherlandHomogeneousCoefficientZero, sutherlandX1Plane25]
  field_simp <;> ring

/-- Every raw point on the chart where the two universal denominators are
nonzero maps to Sutherland's optimized affine model. -/
theorem sutherlandRawToOptimized_on_plane
    {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0)
    (hK : r * s - 2 * r + 1 ≠ 0) (hB : s ^ 2 - s - r + 1 ≠ 0) :
    sutherlandX1Plane25
        ((s - r) / (r * s - 2 * r + 1))
        ((r * s - 2 * r + 1) / (s ^ 2 - s - r + 1)) = 0 := by
  have hidentity := sutherlandRawToOptimized_bihomogeneous_identity r s
  rw [sutherlandBihomogenized25_eq_affine _ _ _ _ hK hB, hraw,
    mul_zero] at hidentity
  simpa using (mul_eq_zero.mp hidentity).resolve_left
    (mul_ne_zero (pow_ne_zero 8 hK) (pow_ne_zero 8 hB))

/-- The raw formula `(s-r)/(r*s-2*r+1)` simplifies to `X/K` in Tate
coordinates. -/
theorem tateToSutherlandX_eq_raw
    {b c : ℚ} (hc : c ≠ 0) (hd : b - c ≠ 0)
    (hK : tateToSutherlandCommon25 b c ≠ 0) :
    (c ^ 2 / (b - c) - b / c) /
        ((b / c) * (c ^ 2 / (b - c)) - 2 * (b / c) + 1) =
      tateToSutherlandXNum25 b c / tateToSutherlandCommon25 b c := by
  have hK' : -2 * b ^ 2 + b * c ^ 2 + 3 * b * c - c ^ 2 ≠ 0 := by
    simpa [tateToSutherlandCommon25] using hK
  simp only [tateToSutherlandXNum25, tateToSutherlandCommon25]
  field_simp [hc, hd, hK']
  ring

/-- Every primitive Tate solution maps to Sutherland's optimized affine
`X₁(25)` model by the explicit formulas
`x=X/K` and `y=K(b-c)/B`.  The assumptions are exactly the nonzero Tate
parameter, the proper-order-five exclusion, and the primitive equation. -/
theorem _root_.solution
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    sutherlandX1Plane25
        (tateToSutherlandXNum25 b c / tateToSutherlandCommon25 b c)
        (tateToSutherlandCommon25 b c * (b - c) /
          tateToSutherlandYDen25 b c) = 0 := by
  have hc := tateC_ne_zero_of_F25 hb hF
  have hd : b - c ≠ 0 := by
    simpa [TateNFDivision.F5] using h5
  let r := b / c
  let s := c ^ 2 / (b - c)
  have hraw : sutherlandRawX1Plane25 r s = 0 :=
    sutherlandRawX1Plane25_zero_of_tate hF hc hd
  have hr1 : r ≠ 1 := tateR_ne_one hc hd
  have hKraw : r * s - 2 * r + 1 ≠ 0 :=
    sutherlandCommon_ne_zero_on_raw hraw hr1
  have hs0 : s ≠ 0 := div_ne_zero (pow_ne_zero 2 hc) hd
  have hs1 : s ≠ 1 := sutherlandS_ne_one_on_raw hraw hr1
  have hBraw : s ^ 2 - s - r + 1 ≠ 0 :=
    sutherlandYDen_ne_zero_on_raw hraw hs0 hs1
  have hplane := sutherlandRawToOptimized_on_plane hraw hKraw hBraw
  have hK := tateToSutherlandCommon_ne_zero hF hc hd
  have hB := tateToSutherlandYDen_ne_zero hF hc hd
  rw [tateToSutherlandX_eq_raw hc hd hK,
    tateToSutherlandY_eq_raw hc hd hB] at hplane
  exact hplane

end MazurProof.RationalPointsN25SutherlandBridge
