-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.algebraMap_smul_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:43:06.502675+00:00
-- url     : https://prove2.me/submissions/38ea9073-1f29-4a8f-90b7-c12fa150739b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (p q : F[X]) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X) =
      algebraMap F[X] W.toAffine.FunctionField p +
        algebraMap F[X] W.toAffine.FunctionField q * genY W := by
  rw [map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rfl
end GroundTheory.Arith.Abelian
