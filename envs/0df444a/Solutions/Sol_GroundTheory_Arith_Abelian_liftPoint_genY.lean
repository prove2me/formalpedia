-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.liftPoint_genY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:42.025159+00:00
-- url     : https://prove2.me/submissions/8facfd79-ad92-44f0-acca-fa0f8073d38a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Theorems.Thm_GroundTheory_Arith_Abelian_evalAt_mk
import Theorems.Thm_GroundTheory_Arith_Abelian_liftPoint_algebraMap
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
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable {L : Type*} [Field L] [Algebra F L] {u v : L}
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (h : (W.baseChange L).toAffine.Equation u v) (hu : Transcendental F u) :
    liftPoint W h hu (genY W) = v := by
  rw [genY, liftPoint_algebraMap, evalAt_mk]
  simp
end GroundTheory.Arith.Abelian
