-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.normalizedIdealPair_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:22:44.985796+00:00
-- url     : https://prove2.me/submissions/cbab48b1-8aef-469a-be14-0d2bda9b594d

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_TruncatedSecondTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_LogDensity
import Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_quadraticRow_squared


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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (lengthScale : Ideal O) :
    normalizedIdealPair I J lengthScale ^ 2 =
      (idealZeroMask I (idealGenerator lengthScale) * idealZeroMask J (idealGenerator lengthScale)) / (Ideal.absNorm lengthScale : ℂ) := by
  have hc : unrestrictedPairCharacter I J lengthScale ^ 2 =
      idealZeroMask I (idealGenerator lengthScale) * idealZeroMask J (idealGenerator lengthScale) := by
    unfold unrestrictedPairCharacter
    calc
      _ = (quadraticRow I (idealGenerator lengthScale) * quadraticRow I (idealGenerator lengthScale)) *
        (quadraticRow J (idealGenerator lengthScale) * quadraticRow J (idealGenerator lengthScale)) := by ring
      _ = _ := by rw [canonical_quadraticRow_squared I hI, canonical_quadraticRow_squared J hJ]
  have hn : (Real.sqrt (Ideal.absNorm lengthScale : ℝ) : ℂ) ^ 2 = (Ideal.absNorm lengthScale : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Ideal.absNorm lengthScale) : (0 : ℝ) ≤ _)
  rw [normalizedIdealPair, div_pow, hc, hn]
end OAI.CanonicalQuadraticSieve
