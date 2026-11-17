-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF2.zChart_jacobian_certificate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:29.313707+00:00
-- url     : https://prove2.me/submissions/f4556d60-ad71-4063-a359-efc752862a2e

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Structural Jacobian certificates for the canonical curve in both good characteristics. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

/-- Bézout certificate excluding a singular point on the chart `z=1`. -/
theorem _root_.solution
    {K : Type*} [CommRing K] [CharP K 2] (x y w : K) :
    let P : Coordinates4 K := ⟨x, y, 1, w⟩
    let q := canonicalQuadric25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (x^2 + x*y + x*w + y) * q +
      (x*w + w^2 + w + 1) * M.xy +
      (x^2 + x*w + x + w) * M.xz +
      (x^2*w + w^3 + x*y + y*w + w^2 + w) * M.xw +
      (x*w + w^2 + y + w + 1) * M.yz +
      (x^2*w + w^3 + x*y + x*w + y*w + y + w + 1) * M.yw +
      (x*w + w^2 + y + 1) * M.zw = 1 := by
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
  ring_nf
  simp [htwo, hfour, hsix]

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
