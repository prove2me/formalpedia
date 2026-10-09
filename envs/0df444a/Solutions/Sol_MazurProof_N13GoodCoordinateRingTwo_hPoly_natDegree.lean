-- Prove2me | solution 1 for MazurProof.N13GoodCoordinateRingTwo.hPoly_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:30:24.690544+00:00
-- url     : https://prove2.me/submissions/e4494a9c-a9be-4276-bc17-64411515d404

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
theorem hPoly_natDegree : hPoly.natDegree = 3 := by
  unfold hPoly
  (compute_degree; norm_num)
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

theorem solution : type_of% @MazurProof.N13GoodCoordinateRingTwo.hPoly_natDegree := @MazurProof.N13GoodCoordinateRingTwo.hPoly_natDegree
