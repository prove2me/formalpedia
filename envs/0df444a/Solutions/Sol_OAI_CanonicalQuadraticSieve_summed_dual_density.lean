-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.summed_dual_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:47:29.951273+00:00
-- url     : https://prove2.me/submissions/a9c2652e-d5f0-40fc-8a88-40c9df540345

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Theorems.Thm_OAI_CanonicalQuadraticSieve_unrestrictedPrincipalDensity_twisted_squarefree
import Theorems.Thm_OAI_CanonicalQuadraticSieve_densityPairSum_weighted_sum

set_option autoImplicit false
open OAI
noncomputable section
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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
        (fun j => a j*quadraticRow (cols j) (idealGenerator q))
        (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ))) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedPairDivisors I J G) := by
  simp_rw [unrestrictedPrincipalDensity_twisted_squarefree cols a _ M K hM hcols]
  calc
    _ = (Real.sqrt M : ℂ)*∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        densityPairSum cols a (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      rw [densityPairSum_weighted_sum]
      rfl
end OAI.CanonicalQuadraticSieve
