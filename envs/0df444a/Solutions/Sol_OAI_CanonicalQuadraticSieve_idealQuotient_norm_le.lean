-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.idealQuotient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:07:35.517812+00:00
-- url     : https://prove2.me/submissions/3c842854-fa24-4386-84b4-fccbf28ea365

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_mul

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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution {D I : Ideal O} (hD0 : D ≠ 0) (hD : D ∣ I)
    (N : ℝ) (hN : (Ideal.absNorm I : ℝ) ≤ N) :
    (Ideal.absNorm (idealQuotient D I) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hp : (0 : ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hD0 (Ideal.absNorm_eq_zero_iff.mp h))
  apply (le_div_iff₀ hp).mpr
  calc
    _ = (Ideal.absNorm (D * idealQuotient D I) : ℝ) := by
      rw [map_mul, Nat.cast_mul, mul_comm]
    _ = (Ideal.absNorm I : ℝ) := by rw [idealQuotient_mul hD]
    _ ≤ N := hN
end OAI.CanonicalQuadraticSieve
