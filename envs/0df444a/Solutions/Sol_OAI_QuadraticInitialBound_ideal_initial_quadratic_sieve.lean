-- Prove2me | solution 1 for OAI.QuadraticInitialBound.ideal_initial_quadratic_sieve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:43:06.172462+00:00
-- url     : https://prove2.me/submissions/acefb184-2e74-4b47-ae17-c7b05344b508

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Theorems.Thm_OAI_QuadraticInitialBound_diagonalControl_nonneg
import Theorems.Thm_OAI_QuadraticInitialBound_quadratic_initial_finite_bound
import Theorems.Thm_OAI_CompactScaleBridge_idealsUpTo_card_le
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealSupport_injective_on_squarefree
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealSupport_product_eq
import Theorems.Thm_OAI_QuadraticInitialBound_pvControl_nonneg


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
open scoped BigOperators Classical SchwartzMap
open OAI.QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge
namespace OAI.QuadraticInitialBound
theorem _root_.solution
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hsq : ∀ I ∈ F, Squarefree I)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (N : ℕ) (hN : 1 ≤ N) (hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (a : Ideal O → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 3‖ ^ 2) ≤
      initialSieveConstant * (M + (N : ℝ) ^ 2) * ∑ I ∈ F, ‖a I‖ ^ 2 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsupp : Set.InjOn (idealSupport F) (↑F : Set (Ideal O)) := by
    intro I hI J hJ h
    exact idealSupport_injective_on_squarefree F hI hJ (hsq I hI) (hsq J hJ) h
  have hNorm (I : Ideal O) (hI : I ∈ F) :
      supportNorm (fun i : primePool F => i.val) (idealSupport F I) ≤ (N : ℝ) := by
    unfold supportNorm
    rw [idealSupport_product_eq F hI (hsq I hI)]
    exact_mod_cast hnorm I hI
  have hb := quadratic_initial_finite_bound (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood) hchar F (idealSupport F) hsupp
    (N : ℝ) (by positivity) hNorm a M hM R hR
  change (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 3‖ ^ 2) ≤
    (diagonalControl sieveCutoff * M + pvControl sieveCutoff * (N : ℝ) * F.card) *
      ∑ I ∈ F, ‖a I‖ ^ 2 at hb
  have hsub : F ⊆ idealsUpTo N := by
    intro I hI
    apply mem_idealsUpTo.mpr
    constructor
    · apply Nat.one_le_iff_ne_zero.mpr
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hFpos I hI
    · exact hnorm I hI
  have hcardNat : F.card ≤ 64 * (N + 1) :=
    (Finset.card_le_card hsub).trans (CompactScaleBridge.idealsUpTo_card_le N)
  have hcard : (F.card : ℝ) ≤ 128 * (N : ℝ) := by
    have hh : (F.card : ℝ) ≤ 64 * ((N : ℝ) + 1) := by exact_mod_cast hcardNat
    linarith
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hpv := pvControl_nonneg sieveCutoff
  have hmul := mul_le_mul_of_nonneg_left hcard (mul_nonneg hpv (by positivity : (0 : ℝ) ≤ N))
  unfold initialSieveConstant
  nlinarith [mul_nonneg hdiag (sq_nonneg (N : ℝ)),
    mul_nonneg hpv (show 0 ≤ M by linarith)]
end OAI.QuadraticInitialBound
