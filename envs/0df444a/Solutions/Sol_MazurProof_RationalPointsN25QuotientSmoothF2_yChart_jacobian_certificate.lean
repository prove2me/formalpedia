-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF2.yChart_jacobian_certificate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:00.369141+00:00
-- url     : https://prove2.me/submissions/b18d415c-7e75-48b7-ab3b-8756781f16d6

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Structural Jacobian certificates for the canonical curve in both good characteristics. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

/-- Bézout certificate excluding a singular point on the chart `y=1`. -/
theorem _root_.solution
    {K : Type*} [CommRing K] [CharP K 2] (x z w : K) :
    let P : Coordinates4 K := ⟨x, 1, z, w⟩
    let q := canonicalQuadric25CharTwo P
    let k := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (x*z^2*w + z^3*w + x*z*w^2 + z^2*w^2 + z*w^3 +
        x*z^2 + z^3 + x*z*w + z^2*w + x*w + z + 1) * q +
      (x*z*w + z^2*w + z*w^2 + x*w) * k +
      (x*z*w + z^2*w + z*w^2 + z^2 + x*w) * M.xy +
      (x^2*z + x*z^2 + x*z*w + z^2*w + x^2 + z^2 + x + z) * M.xz +
      (z*w^2 + z^2 + z + w + 1) * M.yz +
      (z*w) * M.yw = 1 := by
  dsimp [canonicalQuadric25CharTwo, canonicalCubic25CharTwo,
    canonicalJacobianMinors25CharTwo, canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hfour : (4 : K) = 0 := by
    calc
      (4 : K) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo, add_zero]
  have hsix : (6 : K) = 0 := by
    calc
      (6 : K) = 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  have height : (8 : K) = 0 := by
    calc
      (8 : K) = 2 + 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  have hten : (10 : K) = 0 := by
    calc
      (10 : K) = 2 + 2 + 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  ring_nf
  simp [htwo, hfour, hsix, height, hten]

end MazurProof.RationalPointsN25QuotientSmoothF2

namespace MazurProof.RationalPointsN25QuotientSmoothF3

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThree

open MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientSmallThreeSemantic

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
