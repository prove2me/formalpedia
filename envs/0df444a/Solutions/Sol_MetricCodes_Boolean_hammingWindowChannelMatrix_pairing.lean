-- Prove2me | solution 1 for MetricCodes.Boolean.hammingWindowChannelMatrix_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/fa1148b1-8a0b-4ed8-83b4-a7967b2694b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_isLevel_hammingWindowBasis
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_restricted_coordinateDot

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ)
    (Q R : HammingWindowIndex n k L) :
    (∑ p : Fin n × HammingWindowIndex n k L,
      hammingWindowChannelMatrix n k L v lam p Q *
        hammingWindowChannelMatrix n k L v lam p R) =
      ∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R)) := by
  classical
  unfold hammingWindowChannelMatrix
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro target _
  calc
    (∑ S : Level n (k + target.val),
      ∑ a : Fin n,
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q) a S.val) *
        (hammingAdjacentBlockCoefficient n k L v lam target R.1 *
          hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R) a S.val)) =
      (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
        hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        (∑ a : Fin n,
          ∑ S : Level n (k + target.val),
            hammingAdjacentChannel n k L target Q.1
                (hammingWindowBasis n k L Q) a S.val *
              hammingAdjacentChannel n k L target R.1
                (hammingWindowBasis n k L R) a S.val) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          ring
    _ = (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
        hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R)) := by
          rw [hammingAdjacentChannel_restricted_coordinateDot
            n k L target Q.1 R.1
            (hammingWindowBasis n k L Q)
            (hammingWindowBasis n k L R)
            (isLevel_hammingWindowBasis n k L Q)
            (isLevel_hammingWindowBasis n k L R)]
end MetricCodes.Boolean
