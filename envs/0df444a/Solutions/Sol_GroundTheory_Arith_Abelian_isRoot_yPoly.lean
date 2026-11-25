-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.isRoot_yPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:43:46.707963+00:00
-- url     : https://prove2.me/submissions/76f43400-b146-4b01-9bb7-6a70368fa843

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {x y : F} (h : E.toAffine.Equation x y) : (yPoly E x).IsRoot y := by
  rw [equation_iff] at h
  simp only [yPoly, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination h
end GroundTheory.Arith.Abelian
