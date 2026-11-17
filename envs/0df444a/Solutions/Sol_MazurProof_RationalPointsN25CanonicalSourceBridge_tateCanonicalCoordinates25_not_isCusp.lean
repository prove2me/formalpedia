-- Prove2me | solution 1 for MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_not_isCusp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:39.9293+00:00
-- url     : https://prove2.me/submissions/a478d873-730a-4f93-9f2e-e58a50d2cb71

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25CanonicalPoints
import Definitions.Def_RationalPointsN25CanonicalSourceBridge
import Definitions.Def_RationalPointsN25QuotientAction
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOrder25Factor
import Theorems.Thm_MazurProof_RationalPointsN25CanonicalSourceBridge_sutherlandCanonicalCoordinates25_not_isCusp
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherlandY_eq_raw
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateC_ne_zero_of_F25
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherland_on_plane
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandS_ne_one_on_raw
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandYDen_ne_zero_on_raw
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawX1Plane25_zero_of_tate
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateR_ne_one
import Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherlandYDen_ne_zero

/-! Proofs of the lemmas stated in `Theorems.Thm_CanonicalLevelTwentyFive_SutherlandToCanonical` and their helpers. -/

namespace MazurProof.RationalPointsN25CanonicalSourceBridge

open RationalPointsN25CanonicalPoints

open RationalPointsN25QuotientAction

open RationalPointsN25SutherlandBridge

open TateOrder25Factor

/-- The raw source equation on its diagonal consists only of the two boundary
factors `t⁴(t-1)¹⁷`.  This specialization excludes `r=s` on the primitive
raw Tate chart. -/
theorem sutherlandRawX1Plane25_diagonal (t : ℚ) :
    sutherlandRawX1Plane25 t t = t ^ 4 * (t - 1) ^ 17 := by
  simp only [sutherlandRawX1Plane25, sutherlandRawCoefficientTen, sutherlandRawCoefficientNine, sutherlandRawCoefficientEight, sutherlandRawCoefficientSeven, sutherlandRawCoefficientSix, sutherlandRawCoefficientFive, sutherlandRawCoefficientFour, sutherlandRawCoefficientThree, sutherlandRawCoefficientTwo, sutherlandRawCoefficientOne, sutherlandRawCoefficientZero]
  ring

/-- The optimized second coordinate is not one on the primitive Tate locus.
If it were one, the raw optimization formula would force either `s=1` or
`r=s`; the diagonal specialization excludes the latter as well. -/
theorem tateSutherlandYCoordinate25_ne_one
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    tateSutherlandYCoordinate25 b c ≠ 1 := by
  have hc := tateC_ne_zero_of_F25 hb hF
  have hd : b - c ≠ 0 := by
    simpa [TateNFDivision.F5] using h5
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hraw : sutherlandRawX1Plane25 r s = 0 :=
    sutherlandRawX1Plane25_zero_of_tate hF hc hd
  have hr1 : r ≠ 1 := tateR_ne_one hc hd
  have hs0 : s ≠ 0 := div_ne_zero (pow_ne_zero 2 hc) hd
  have hs1 : s ≠ 1 := sutherlandS_ne_one_on_raw hraw hr1
  have hBraw : s ^ 2 - s - r + 1 ≠ 0 :=
    sutherlandYDen_ne_zero_on_raw hraw hs0 hs1
  have hB := tateToSutherlandYDen_ne_zero hF hc hd
  have hyEq :
      (r * s - 2 * r + 1) / (s ^ 2 - s - r + 1) =
        tateSutherlandYCoordinate25 b c := by
    simpa [r, s, tateSutherlandYCoordinate25] using
      (tateToSutherlandY_eq_raw hc hd hB)
  intro hy1
  have hquot : (r * s - 2 * r + 1) / (s ^ 2 - s - r + 1) = 1 := by
    rw [hyEq, hy1]
  have hnum : r * s - 2 * r + 1 = s ^ 2 - s - r + 1 := by
    exact (div_eq_one_iff_eq hBraw).mp hquot
  have hfactor : (s - 1) * (r - s) = 0 := by
    calc
      (s - 1) * (r - s) =
          (r * s - 2 * r + 1) - (s ^ 2 - s - r + 1) := by ring
      _ = 0 := sub_eq_zero.mpr hnum
  rcases mul_eq_zero.mp hfactor with hs | hrs
  · exact hs1 (sub_eq_zero.mp hs)
  · have hrs' : r = s := sub_eq_zero.mp hrs
    rw [hrs'] at hraw
    rw [sutherlandRawX1Plane25_diagonal] at hraw
    rcases mul_eq_zero.mp hraw with hs | hs
    · exact hs0 ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hs)
    · exact hs1 (sub_eq_zero.mp
        ((pow_eq_zero_iff (by norm_num : (17 : ℕ) ≠ 0)).mp hs))

/-- Every primitive order-25 Tate solution maps outside the five canonical
cusp classes.  Both hypotheses needed by the source-side certificate follow
from the already checked Tate-to-Sutherland comparison. -/
theorem _root_.solution
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    ¬ IsCusp25 (tateCanonicalCoordinates25 b c) := by
  apply sutherlandCanonicalCoordinates25_not_isCusp
  · simpa [tateSutherlandXCoordinate25, tateSutherlandYCoordinate25] using
      (tateToSutherland_on_plane hb h5 hF)
  · exact tateSutherlandYCoordinate25_ne_one hb h5 hF

end MazurProof.RationalPointsN25CanonicalSourceBridge
