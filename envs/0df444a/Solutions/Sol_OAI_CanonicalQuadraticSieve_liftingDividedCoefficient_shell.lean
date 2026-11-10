-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.liftingDividedCoefficient_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:13:56.404114+00:00
-- url     : https://prove2.me/submissions/a57e8674-6352-4e38-a1dd-1c80fb1e65c2

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Theorems.Thm_OAI_CanonicalQuadraticSieve_liftingQuotientColumn_injective
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_norm_eq
import Theorems.Thm_OAI_CanonicalQuadraticSieve_liftingPrime_norm
import Theorems.Thm_OAI_CanonicalQuadraticSieve_liftingPrime_prime
import Theorems.Thm_OAI_FiniteSieveRestriction_extendByZero_apply_image
import Theorems.Thm_OAI_FiniteSieveRestriction_extendByZero_zero


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
theorem _root_.solution (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N (X/7) (liftingDividedCoefficient N a) := by
  classical
  intro J hJ
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have he : liftingDividedCoefficient N a (liftingQuotientColumn N I)=a I.val :=
    extendByZero_apply_image _ _ _ (liftingQuotientColumn_injective N).injOn I (Finset.mem_univ I)
  have hn : a I.val≠0 := by rwa [he] at hJ
  have hs := ha I.val hn
  change (X/7)/2<(Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ) ∧
    (Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ)≤X/7
  rw [idealQuotient_norm_eq liftingPrime I.val.val liftingPrime_prime.ne_zero
    (Finset.mem_filter.mp I.property).2,liftingPrime_norm]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith
end OAI.CanonicalQuadraticSieve
