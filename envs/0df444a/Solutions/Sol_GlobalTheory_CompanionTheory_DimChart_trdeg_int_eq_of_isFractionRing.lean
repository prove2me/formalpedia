-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DimChart.trdeg_int_eq_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:01:12.865045+00:00
-- url     : https://prove2.me/submissions/4cfc26f0-80c6-479a-a1a9-9e19d9ea0e2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KrullDimQuotientEqTrdegSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DimChart
namespace GlobalTheory.CompanionTheory.DimChart
theorem _root_.solution (A : Type) [CommRing A] [IsDomain A] [Algebra ℤ A] (L : Type)
    [Field L] [Algebra ℤ L] [Algebra A L] [IsFractionRing A L]
    (hA : Function.Injective (algebraMap ℤ A)) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ L := by
  obtain rfl : ‹Algebra ℤ A› = Ring.toIntAlgebra A := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  have : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A L)
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).2 hA
  have : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  rw [← trdeg_add_eq ℤ A (A := L), trdeg_eq_zero (R := A) (A := L), add_zero]
end GlobalTheory.CompanionTheory.DimChart
