-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF3.normalized_projective_point_not_singular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:21.563288+00:00
-- url     : https://prove2.me/submissions/b7b6c2ac-fea3-4d91-8235-2437cb7a4ab1

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_zChart_yw_minor_eq_one25Three
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_yChart_quadric25Three
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_exceptional_xChart_jacobian_certificate25Three
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_regular_yw_minor_identity25Three
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_yChart_cubic25Three
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_residual_regular_bezout25Three
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_regular_zw_minor_identity25Three
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_wChart_xz_minor_eq_one25Three
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_yChart_xw_minor_second_branch25Three
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_yChart_xy_minor_zero_branch25Three

/-! Structural Jacobian certificates for the canonical curve in both good characteristics. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

end MazurProof.RationalPointsN25QuotientSmoothF2

namespace MazurProof.RationalPointsN25QuotientSmoothF3

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThree

open MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientSmallThreeSemantic

/-! ## Algebraic-closure-valid projective consequence -/

/-- No normalized projective point over any characteristic-three field is
singular for the canonical quadric-cubic complete intersection.  Since the
field is arbitrary, applying the theorem over an algebraic closure proves
geometric Jacobian nonsingularity rather than only absence of rational
singular points. -/
theorem _root_.solution
    {K : Type*} [Field K] [CharP K 3] (P : NormalizedProjective4 K) :
    ¬ IsCanonicalSingular25Three (normalizedCoordinatesThree P) := by
  intro hs
  cases P with
  | xChart y z w =>
      change IsCanonicalSingular25Three
        (⟨1, y, z, w⟩ : Coordinates4 K) at hs
      rcases hs with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
      by_cases hz : z = 1
      · subst z
        have hq' : y ^ 2 + y - 1 = 0 := by
          dsimp [canonicalQuadric25Three] at hq
          linear_combination hq
        have hc' : y + w - w ^ 2 = 0 := by
          dsimp [canonicalCubic25Three] at hc
          linear_combination hc
        have hm' : (1 - y) * (1 + w) = 0 := by
          dsimp [canonicalJacobianMinors25Three,
            canonicalQuadricGradient25Three,
            canonicalCubicGradient25Three] at hyw
          linear_combination hyw
        have hcert := exceptional_xChart_jacobian_certificate25Three y w
        rw [hq', hc', hm'] at hcert
        norm_num at hcert
      · have hcurve : IsCanonicalNormalizedThree (.xChart y z w) := ⟨hq, hc⟩
        have hQC := (isCanonicalNormalizedThree_xChart_iff y z w).1 hcurve
        have hB :=
          (canonicalCubicX25Three_eq_zero_iff_residual hz hQC.1).1 hQC.2
        have hByProd :
            (z - 1) * canonicalResidualYDerivative25Three y z = 0 := by
          have hid := regular_yw_minor_identity25Three y z w
          dsimp only at hid
          rw [hQC.1, hyw] at hid
          simp only [zero_mul, mul_zero, zero_add] at hid
          exact hid.symm
        have hBzProd :
            (z - 1) * canonicalResidualZDerivative25Three y z = 0 := by
          have hid := regular_zw_minor_identity25Three y z w
          dsimp only at hid
          rw [hQC.1, hQC.2, hzw] at hid
          simp only [zero_mul, mul_zero, zero_add, add_zero] at hid
          exact hid.symm
        have hD : z - 1 ≠ 0 := sub_ne_zero.mpr hz
        have hBy : canonicalResidualYDerivative25Three y z = 0 :=
          (mul_eq_zero.mp hByProd).resolve_left hD
        have hBz : canonicalResidualZDerivative25Three y z = 0 :=
          (mul_eq_zero.mp hBzProd).resolve_left hD
        have hcert := residual_regular_bezout25Three y z
        rw [hB, hBy, hBz] at hcert
        simp only [mul_zero, zero_add] at hcert
        exact hz (sub_eq_zero.mp hcert.symm)
  | yChart z w =>
      change IsCanonicalSingular25Three
        (⟨0, 1, z, w⟩ : Coordinates4 K) at hs
      rcases hs with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
      rw [yChart_quadric25Three] at hq
      rw [yChart_cubic25Three] at hc
      have hz : z ≠ 0 := by
        intro hz
        subst z
        norm_num at hq
      rcases mul_eq_zero.mp hc with hzw' | hfactor
      · have hw : w = 0 := (mul_eq_zero.mp hzw').resolve_left hz
        have hzval : z = -1 := by
          rw [hw] at hq
          linear_combination hq
        rw [hw, hzval] at hxy
        rw [yChart_xy_minor_zero_branch25Three] at hxy
        exact one_ne_zero hxy
      · have hwval : w = 1 + z := by linear_combination -hfactor
        rw [hwval] at hq hxw
        have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
        have hrel : z ^ 2 - z + 1 = 0 := by
          linear_combination hq - z * h3
        rw [yChart_xw_minor_second_branch25Three] at hxw
        have : (1 : K) = 0 := by linear_combination hrel - hxw
        exact one_ne_zero this
  | zChart w =>
      change IsCanonicalSingular25Three
        (⟨0, 0, 1, w⟩ : Coordinates4 K) at hs
      rcases hs with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
      rw [zChart_yw_minor_eq_one25Three] at hyw
      exact one_ne_zero hyw
  | wChart =>
      change IsCanonicalSingular25Three
        (⟨0, 0, 0, 1⟩ : Coordinates4 K) at hs
      rcases hs with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
      rw [wChart_xz_minor_eq_one25Three] at hxz
      exact one_ne_zero hxz

end MazurProof.RationalPointsN25QuotientSmoothF3

namespace N25

open scoped BigOperators

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

end N25

namespace N25

end N25
