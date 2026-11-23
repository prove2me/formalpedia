-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Phi_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:51.652804+00:00
-- url     : https://prove2.me/submissions/dd58fc98-0377-46dc-8e30-c45887bd04af

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
section Sequence
variable {R : Type*} [CommRing R] [IsDomain R]
end Sequence
section Values
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
private theorem evalEval_mkW {x y : R} (h : W.toAffine.Equation x y) (g : R[X][Y]) :
    AdjoinRoot.evalEval (p := W.toAffine.polynomial) h (Affine.CoordinateRing.mk W g) =
      g.evalEval x y :=
  AdjoinRoot.evalEval_mk h g
end Values
section Algebra
variable {F : Type*} [Field F]
end Algebra
section Points
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [DecidableEq F]
end Points
section Main
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
end Main
section Statements
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
end Statements
end GroundTheory.Arith.Abelian
end

set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.Φ n).eval x = x * psiAt W x y n ^ 2 - psiAt W x y (n + 1) * psiAt W x y (n - 1) := by
  have := congrArg (AdjoinRoot.evalEval (p := W.toAffine.polynomial) h)
    (Affine.CoordinateRing.mk_φ W n)
  rw [evalEval_mkW W h, evalEval_mkW W h, evalEval_C, WeierstrassCurve.φ] at this
  rw [← this, psiAt, psiAt, psiAt]
  simp only [evalEval_sub, evalEval_mul, evalEval_pow, evalEval_C, eval_X]
end GroundTheory.Arith.Abelian
