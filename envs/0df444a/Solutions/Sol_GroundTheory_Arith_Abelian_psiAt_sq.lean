-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.psiAt_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:30.36626+00:00
-- url     : https://prove2.me/submissions/102225da-5246-4f4f-a3aa-510c3d1990f8

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
    psiAt W x y n ^ 2 = (W.ΨSq n).eval x := by
  have := congrArg (AdjoinRoot.evalEval (p := W.toAffine.polynomial) h)
    (Affine.CoordinateRing.mk_Ψ_sq W n)
  rw [← Affine.CoordinateRing.mk_ψ, map_pow, evalEval_mkW W h, evalEval_mkW W h, evalEval_C] at this
  exact this
end GroundTheory.Arith.Abelian
