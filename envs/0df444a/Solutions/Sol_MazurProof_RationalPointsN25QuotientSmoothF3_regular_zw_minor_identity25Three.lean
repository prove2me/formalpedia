-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF3.regular_zw_minor_identity25Three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:31.652196+00:00
-- url     : https://prove2.me/submissions/f564bd3b-2398-4c54-9021-d403cecf528b

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

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

/-- Small numeral reductions reused when ring normalization exposes integer
coefficients in the differentiated elimination identities. -/
private theorem characteristicThree_small_casts
    (K : Type*) [Field K] [CharP K 3] :
    (2 : K) = -1 ∧ (4 : K) = 1 ∧ (5 : K) = 2 ∧
      (6 : K) = 0 ∧ (7 : K) = 1 ∧ (8 : K) = 2 ∧
      (9 : K) = 0 ∧ (10 : K) = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h2 : (2 : K) = -1 := by linear_combination h3
  have h4 : (4 : K) = 1 := by
    calc
      (4 : K) = (3 : K) + 1 := by norm_num
      _ = 1 := by rw [h3, zero_add]
  have h5 : (5 : K) = 2 := by
    calc
      (5 : K) = (3 : K) + 2 := by norm_num
      _ = 2 := by rw [h3, zero_add]
  have h6 : (6 : K) = 0 := by
    calc
      (6 : K) = (3 : K) + 3 := by norm_num
      _ = 0 := by rw [h3, add_zero]
  have h7 : (7 : K) = 1 := by
    calc
      (7 : K) = (3 : K) + 3 + 1 := by norm_num
      _ = 1 := by rw [h3, zero_add, zero_add]
  have h8 : (8 : K) = 2 := by
    calc
      (8 : K) = (3 : K) + 3 + 2 := by norm_num
      _ = 2 := by rw [h3, zero_add, zero_add]
  have h9 : (9 : K) = 0 := by
    calc
      (9 : K) = (3 : K) + 3 + 3 := by norm_num
      _ = 0 := by rw [h3, zero_add, add_zero]
  have h10 : (10 : K) = 1 := by
    calc
      (10 : K) = (3 : K) + 3 + 3 + 1 := by norm_num
      _ = 1 := by rw [h3, zero_add, zero_add, zero_add]
  exact ⟨h2, h4, h5, h6, h7, h8, h9, h10⟩

/-- Differentiating in `z` and `w` gives the companion identity for the
`zw` minor.  The extra cubic term comes from differentiating `(z-1)²`. -/
theorem _root_.solution
    {K : Type*} [Field K] [CharP K 3] (y z w : K) :
    let P : Coordinates4 K := ⟨1, y, z, w⟩
    let M := canonicalJacobianMinors25Three P
    (z - 1) ^ 2 * M.zw =
      canonicalQuadricX25Three y z w *
        ((y + w - 1) * (-z ^ 2 + z) -
          (z - 1) * (y ^ 2 + y * z + z * w + y + w - 1)) +
      (z - 1) * canonicalResidualZDerivative25Three y z +
      2 * (z - 1) ^ 2 * canonicalCubicX25Three y z w := by
  dsimp [canonicalJacobianMinors25Three, canonicalQuadricGradient25Three,
    canonicalCubicGradient25Three, canonicalQuadricX25Three,
    canonicalCubicX25Three, canonicalResidualZDerivative25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  obtain ⟨h2, h4, h5, h6, h7, h8, h9, h10⟩ :=
    characteristicThree_small_casts K
  ring_nf
  simp [h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

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
