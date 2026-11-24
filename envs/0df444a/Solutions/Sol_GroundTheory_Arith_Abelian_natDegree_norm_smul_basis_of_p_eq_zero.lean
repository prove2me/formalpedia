-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.natDegree_norm_smul_basis_of_p_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:33.220875+00:00
-- url     : https://prove2.me/submissions/95558cda-45b9-400c-b170-52f5fc737d94

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
variable {W}
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {q : F[X]} (hq : q ≠ 0) :
    (Algebra.norm F[X] ((0 : F[X]) • (1 : W.toAffine.CoordinateRing) +
      q • AdjoinRoot.mk W.toAffine.polynomial X)).natDegree = 2 * q.natDegree + 3 := by
  have h := degree_norm_smul_basis (W' := W.toAffine) 0 q
  rw [degree_eq_natDegree hq, degree_zero] at h
  apply natDegree_eq_of_degree_eq_some
  rw [h, max_eq_right (by rw [two_nsmul, WithBot.bot_add]; exact bot_le)]
  norm_cast
end GroundTheory.Arith.Abelian
