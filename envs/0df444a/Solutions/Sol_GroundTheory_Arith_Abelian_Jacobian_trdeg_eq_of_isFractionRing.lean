-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:19:50.126217+00:00
-- url     : https://prove2.me/submissions/c5c613ea-2d43-4b58-9395-9f1a77653101

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian GroundTheory.Arith.Abelian.Jacobian
open Algebra Cardinal
universe u
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A]
omit [Algebra.FiniteType k A]
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution [IsDomain A] (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K] : trdeg k K = trdeg k A := by
  have _ : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A K)
  have _ : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  rw [← trdeg_add_eq k A (A := K), trdeg_eq_zero (R := A) (A := K), add_zero]
end GroundTheory.Arith.Abelian.Jacobian
