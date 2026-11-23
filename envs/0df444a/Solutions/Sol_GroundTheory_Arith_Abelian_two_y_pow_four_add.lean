-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.two_y_pow_four_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:31.61086+00:00
-- url     : https://prove2.me/submissions/2063d00e-5534-4585-b240-60e6fd894b57

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Theorems.Thm_GroundTheory_Arith_Abelian_two_y_sq
import Theorems.Thm_GroundTheory_Arith_Abelian_Psi3_eval
import Theorems.Thm_GroundTheory_Arith_Abelian_prePsi4_eval

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
theorem _root_.solution {x y : R} (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 4 + W.preΨ₄.eval x =
      (6 * x ^ 2 + W.b₂ * x + W.b₄) * W.Ψ₃.eval x := by
  rw [show (2 * y + W.a₁ * x + W.a₃) ^ 4 = ((2 * y + W.a₁ * x + W.a₃) ^ 2) ^ 2 by ring,
    two_y_sq W h, prePsi4_eval, Psi3_eval]
  linear_combination x ^ 2 * W.b_relation
end GroundTheory.Arith.Abelian
