-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.idealQuotient_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:54:21.573202+00:00
-- url     : https://prove2.me/submissions/702d212d-e23d-4aaf-aef9-181605760e07

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_norm_eq

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
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (D I : Ideal O) (hD : D≠0) (hDI : D∣I) (N : ℝ)
    (hI : N/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤N) :
    (N/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (idealQuotient D I):ℝ) ∧
      (Ideal.absNorm (idealQuotient D I):ℝ)≤N/(Ideal.absNorm D:ℝ) := by
  have hn : 0<(Ideal.absNorm D:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  rw [idealQuotient_norm_eq D I hD hDI]
  constructor
  · calc
      _ = (N/2)/(Ideal.absNorm D:ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hI.1 hn.le
  · exact div_le_div_of_nonneg_right hI.2 hn.le
end OAI.CanonicalQuadraticSieve
