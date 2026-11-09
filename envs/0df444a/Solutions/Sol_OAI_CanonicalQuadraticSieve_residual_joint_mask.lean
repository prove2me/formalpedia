-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.residual_joint_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:51:27.203411+00:00
-- url     : https://prove2.me/submissions/7da0f400-6bcf-4359-9b68-40e96b9d46b4

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealZeroMask_commonMaskIdeal
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealZeroMask_idempotent
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_idealQuotient
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_of_dvd
import Theorems.Thm_OAI_CanonicalQuadraticSieve_commonMaskIdeal_squarefree
import Theorems.Thm_OAI_CanonicalQuadraticSieve_gcdMaskPrimes_mask
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_mul
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealZeroMask_mul
import Theorems.Thm_OAI_CanonicalQuadraticSieve_singleton_rowCoprimeMask_eq_idealZeroMask


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (z : O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I*J) => P.val) Finset.univ z =
      rowCoprimeMask (fun P : primePool {commonMaskIdeal D*(idealQuotient D I*idealQuotient D J)} => P.val)
        Finset.univ z := by
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hi : idealZeroMask I z=idealZeroMask D z*idealZeroMask (idealQuotient D I) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D I) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDI).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hIq.1 z
  have hj : idealZeroMask J z=idealZeroMask D z*idealZeroMask (idealQuotient D J) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D J) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDJ).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hJq.1 z
  rw [gcdMaskPrimes_mask,singleton_rowCoprimeMask_eq_idealZeroMask,
    idealZeroMask_mul I J hI.1 hJ.1,
    idealZeroMask_mul (commonMaskIdeal D) _ (commonMaskIdeal_squarefree D).ne_zero (mul_ne_zero hIq.1 hJq.1),
    idealZeroMask_mul _ _ hIq.1 hJq.1,idealZeroMask_commonMaskIdeal,gcdMaskPrimes_mask,hi,hj]
  calc
    _ = (rowCoprimeMask badPrime Finset.univ z)*(idealZeroMask D z*idealZeroMask D z)*
      (idealZeroMask (idealQuotient D I) z*idealZeroMask (idealQuotient D J) z) := by ring
    _ = _ := by rw [idealZeroMask_idempotent]
end OAI.CanonicalQuadraticSieve
