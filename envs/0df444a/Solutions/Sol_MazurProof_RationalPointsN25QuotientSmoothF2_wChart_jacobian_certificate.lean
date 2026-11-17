-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF2.wChart_jacobian_certificate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:59.689203+00:00
-- url     : https://prove2.me/submissions/aa723243-db81-41bd-9b78-d1958305e543

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Structural Jacobian certificates for the canonical curve in both good characteristics. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

/-- Bézout certificate excluding a singular point on the chart `w=1`. -/
theorem _root_.solution
    {K : Type*} [CommRing K] [CharP K 2] (x y z : K) :
    let P : Coordinates4 K := ⟨x, y, z, 1⟩
    let q := canonicalQuadric25CharTwo P
    let k := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (x*z^4 + z^4 + x*y*z + y^2*z + z^3 + x*y + y^2 + x*z + y*z) * q +
      (x*z^2 + x*z + y + z + 1) * k +
      (x*z^3 + x*z^2 + z^3 + x*y + y^2 + z^2 + x + 1) * M.xy +
      (x*z^3 + x*z^2 + z^3 + x*y + y^2 + z^2 + x + z + 1) * M.xz +
      (x*z + x + z) * M.yz +
      (x*z^2 + x*z + z^2) * M.yw +
      (z^2 + 1) * M.zw = 1 := by
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
  ring_nf
  simp [htwo, hfour, hsix, height]

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
