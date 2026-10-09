-- Prove2me | solution 1 for MazurProof.N13GoodModelTwo.affineFiber_derivative
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:40:19.690951+00:00
-- url     : https://prove2.me/submissions/9d992fdd-df83-447c-9f24-7c8ad612ad44

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13GoodModelTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodModelTwo =====
section
/-!
# A good characteristic-two model of `X₁(13)`

The completed-square sextic is not the model to reduce modulo two.  This file
uses the generalized hyperelliptic equation

`y² + (x³+x+1)y = x⁵+x⁴`.

Over the rationals, completing the square gives the existing N13 sextic.
In characteristic two, the affine chart and the chart at infinity both have
nonzero derivative in the second coordinate.  The `F₂`- and `F₄`-point
counts are obtained from Frobenius and the Artin--Schreier map, not by
enumerating field elements.
-/
namespace MazurProof.N13GoodModelTwo
noncomputable section
open scoped CharTwo
open Polynomial
universe u
variable {R : Type u} [CommRing R]
/-! ## The two charts of the weighted projective completion -/
theorem affineFiber_derivative (x : R) :
    (affineFiber x).derivative = 2 * X + C (h x) := by
  simp only [affineFiber, derivative_sub, derivative_add, derivative_pow,
    derivative_X, derivative_mul, derivative_C, zero_mul, zero_add, mul_one,
    sub_zero]
  norm_num [map_natCast]
  rw [C_ofNat]
/-! ## Structural characteristic-two point classification -/
variable {K : Type u} [Field K] [CharP K 2]
/-! ## The fields `F₂` and `F₄` -/
attribute [local instance] MazurProof.N13GoodModelTwo.instFintypeF4
end
end MazurProof.N13GoodModelTwo
end

end

theorem solution : type_of% @MazurProof.N13GoodModelTwo.affineFiber_derivative := @MazurProof.N13GoodModelTwo.affineFiber_derivative
