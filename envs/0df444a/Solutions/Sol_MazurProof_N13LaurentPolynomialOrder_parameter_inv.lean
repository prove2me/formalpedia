-- Prove2me | solution 1 for MazurProof.N13LaurentPolynomialOrder.parameter_inv
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:31:38.407215+00:00
-- url     : https://prove2.me/submissions/5fd3ff56-998d-4118-916d-4ef6ec08996b

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LaurentPolynomialOrder =====
section
/-!
# The order at infinity of a polynomial

The substitution `X = s⁻¹` reverses a polynomial.  Its leading
coefficient becomes the constant coefficient of the reversed polynomial,
so the latter has order zero; the factor `s⁻ⁿ` accounts for the whole
order.  This is the formal local calculation used at the cusps of `X₁(13)`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof
namespace N13LaurentPolynomialOrder
noncomputable section
universe u
variable (K : Type u) [Field K]
@[simp] lemma parameter_inv : (parameter K)⁻¹ = HahnSeries.single (-1 : ℤ) 1 := by
  simp [parameter, HahnSeries.inv_single]
end
end N13LaurentPolynomialOrder
end MazurProof
end

end

theorem solution : type_of% @MazurProof.N13LaurentPolynomialOrder.parameter_inv := @MazurProof.N13LaurentPolynomialOrder.parameter_inv
