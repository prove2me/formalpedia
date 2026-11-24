-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.natDegree_norm_smul_basis_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:28.783238+00:00
-- url     : https://prove2.me/submissions/8af3f9b3-2195-4e59-a20c-b6d3572de82f

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
theorem _root_.solution {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) +
      q • AdjoinRoot.mk W.toAffine.polynomial X)).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  have h := degree_norm_smul_basis (W' := W.toAffine) p q
  rw [degree_eq_natDegree hq, degree_eq_natDegree hp] at h
  apply natDegree_eq_of_degree_eq_some
  rw [h]
  norm_cast
end GroundTheory.Arith.Abelian
