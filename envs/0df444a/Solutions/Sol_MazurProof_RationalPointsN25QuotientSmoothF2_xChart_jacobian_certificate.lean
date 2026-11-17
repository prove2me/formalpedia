-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF2.xChart_jacobian_certificate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:28.78772+00:00
-- url     : https://prove2.me/submissions/f2a650fe-5e27-4e87-935f-6d6ffe367bf6

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Structural Jacobian certificates for the canonical curve in both good characteristics. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

/-- Bézout certificate excluding a singular point on the chart `x=1`. -/
theorem _root_.solution
    {K : Type*} [CommRing K] [CharP K 2] (y z w : K) :
    let P : Coordinates4 K := ⟨1, y, z, w⟩
    let q := canonicalQuadric25CharTwo P
    let k := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (y*z*w + z^2 + z*w + w^2 + y + w) * q +
      (y*z*w + z^2 + y*w + z*w + w^2 + z + w) * k +
      (y*w + y + z + w + 1) * M.xz +
      (y*w + y + z + w + 1) * M.xw +
      (y*z^2*w + z^3 + y^2*w + z^2*w + y*w^2 + z*w^2 +
        y^2 + y*z + y*w + w^2 + y + z + w) * M.yz +
      (y + 1) * M.yw + (y + 1) * M.zw = 1 := by
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
  simp [htwo, hfour]

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
