-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordInfty_Y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:39.685333+00:00
-- url     : https://prove2.me/submissions/5e62f9dd-edcc-40e9-8daf-a1496e6bf59b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_algebraMap

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
theorem _root_.solution :
    ordInfty W (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial X)) = -3 := by
  have hy : AdjoinRoot.mk W.toAffine.polynomial X =
      (0 : F[X]) • (1 : W.toAffine.CoordinateRing) +
        (1 : F[X]) • AdjoinRoot.mk W.toAffine.polynomial X := by
    rw [zero_smul, one_smul, zero_add]
  have hdeg := degree_norm_smul_basis (W' := W.toAffine) (0 : F[X]) 1
  rw [← hy, degree_zero, degree_one] at hdeg
  have hdeg' : (Algebra.norm F[X] (AdjoinRoot.mk W.toAffine.polynomial X)).degree = 3 := by
    rw [hdeg]; rfl
  have h0 : AdjoinRoot.mk W.toAffine.polynomial X ≠ 0 := by
    rw [← basis_one]
    exact (CoordinateRing.basis W.toAffine).ne_zero 1
  rw [ordInfty_algebraMap W h0, natDegree_eq_of_degree_eq_some hdeg']
  norm_num
end GroundTheory.Arith.Abelian
