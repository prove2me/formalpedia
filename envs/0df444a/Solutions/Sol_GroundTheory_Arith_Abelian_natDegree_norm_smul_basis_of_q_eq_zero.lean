-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.natDegree_norm_smul_basis_of_q_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:34.764539+00:00
-- url     : https://prove2.me/submissions/7401c512-d51d-4a0a-81b8-e8d33943741f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_finrank_coordinateRing


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
variable {W}
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {p : F[X]} :
    (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) + (0 : F[X]) •
      AdjoinRoot.mk W.toAffine.polynomial X)).natDegree = 2 * p.natDegree := by
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one, Algebra.norm_algebraMap,
    finrank_coordinateRing, natDegree_pow]
end GroundTheory.Arith.Abelian
