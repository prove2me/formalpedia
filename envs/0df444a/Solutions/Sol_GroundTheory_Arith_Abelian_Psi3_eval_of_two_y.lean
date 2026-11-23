-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Psi3_eval_of_two_y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:52.100501+00:00
-- url     : https://prove2.me/submissions/68cd3bae-5b3b-49c0-a6ab-4191487be96d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Theorems.Thm_GroundTheory_Arith_Abelian_Psi3_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {x y : R} (h : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    W.Ψ₃.eval x = -(W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) ^ 2 := by
  rw [equation_iff] at h
  rw [Psi3_eval]
  simp only [b₂, b₄, b₆, b₈]
  linear_combination (-(W.a₁ ^ 2 + 4 * W.a₂) - 12 * x) * h +
    ((-W.a₁ * W.a₄ + W.a₂ * W.a₃) + (W.a₁ ^ 2 + 2 * W.a₂) * y + (-W.a₁ * W.a₂ + 3 * W.a₃) * x +
      6 * x * y) * hy
end GroundTheory.Arith.Abelian
