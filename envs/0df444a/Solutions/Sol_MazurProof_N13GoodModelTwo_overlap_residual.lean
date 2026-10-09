-- Prove2me | solution 1 for MazurProof.N13GoodModelTwo.overlap_residual
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:30:25.863849+00:00
-- url     : https://prove2.me/submissions/567ce921-3745-4456-8bfb-3145477e504a

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
/-- Clearing the transition denominators identifies the two chart
residuals. -/
theorem overlap_residual
    {x t v : R} (hxt : x * t = 1) :
    affineResidual x (x ^ 3 * v) =
      x ^ 6 * infinityChartResidual t v := by
  have hx6t : x ^ 6 * t = x ^ 5 := by
    calc
      x ^ 6 * t = x ^ 5 * (x * t) := by ring
      _ = x ^ 5 := by rw [hxt, mul_one]
  have hx6t2 : x ^ 6 * t ^ 2 = x ^ 4 := by
    calc
      x ^ 6 * t ^ 2 = x ^ 4 * (x * t) ^ 2 := by ring
      _ = x ^ 4 := by rw [hxt, one_pow, mul_one]
  have hx6t3 : x ^ 6 * t ^ 3 = x ^ 3 := by
    calc
      x ^ 6 * t ^ 3 = x ^ 3 * (x * t) ^ 3 := by ring
      _ = x ^ 3 := by rw [hxt, one_pow, mul_one]
  calc
    affineResidual x (x ^ 3 * v) =
        x ^ 6 * v ^ 2 + (x ^ 6 + x ^ 4 + x ^ 3) * v -
          x ^ 5 - x ^ 4 := by
      simp only [affineResidual, h, rhs]
      ring
    _ = x ^ 6 * v ^ 2 +
          (x ^ 6 + x ^ 6 * t ^ 2 + x ^ 6 * t ^ 3) * v -
          x ^ 6 * t - x ^ 6 * t ^ 2 := by
      rw [hx6t, hx6t2, hx6t3]
    _ = x ^ 6 * infinityChartResidual t v := by
      simp only [infinityChartResidual]
      ring
/-! ## Structural characteristic-two point classification -/
variable {K : Type u} [Field K] [CharP K 2]
/-! ## The fields `F₂` and `F₄` -/
attribute [local instance] MazurProof.N13GoodModelTwo.instFintypeF4
end
end MazurProof.N13GoodModelTwo
end

end

theorem solution : type_of% @MazurProof.N13GoodModelTwo.overlap_residual := @MazurProof.N13GoodModelTwo.overlap_residual
