-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.liftingCoefficient_row_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:13:53.021561+00:00
-- url     : https://prove2.me/submissions/ef430d4d-ca61-4b01-8ee0-161121ecc671

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Theorems.Thm_OAI_CanonicalQuadraticSieve_liftingCoefficient_row_split
import Theorems.Thm_OAI_CanonicalQuadraticSieve_quadraticRow_norm_le_one
import Theorems.Thm_OAI_QuadraticInitialBound_quadraticRow_norm_le_one


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
open scoped BigOperators Classical
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open FiniteSieveRestriction
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    ‖∑J : idealRange N, quadraticRow J.val z*a J‖^2 ≤
      2*(‖∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J‖^2 +
        ‖∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J‖^2) := by
  rw [liftingCoefficient_row_split]
  let u := ∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J
  let v := ∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J
  change ‖u+quadraticRow liftingPrime z*v‖^2≤2*(‖u‖^2+‖v‖^2)
  have hp : ‖quadraticRow liftingPrime z*v‖≤‖v‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one _ _)
  have hn : ‖u+quadraticRow liftingPrime z*v‖≤‖u‖+‖v‖ := by
    linarith [norm_add_le u (quadraticRow liftingPrime z*v)]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖u‖-‖v‖)]
end OAI.CanonicalQuadraticSieve
