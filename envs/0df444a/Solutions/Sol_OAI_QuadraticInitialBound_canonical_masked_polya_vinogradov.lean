-- Prove2me | solution 1 for OAI.QuadraticInitialBound.canonical_masked_polya_vinogradov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:34:55.234435+00:00
-- url     : https://prove2.me/submissions/fba27661-80b3-4ba8-9194-40a312ae73fc

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Theorems.Thm_OAI_QuadraticInitialBound_finiteSexticRow_norm_le_one
import Theorems.Thm_OAI_QuadraticInitialBound_canonical_polya_vinogradov
import Theorems.Thm_OAI_QuadraticInitialBound_norm_ideal_moebius_le_one
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_masked_radial_dilations
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubset_reducedScale_pos
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk



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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap
open OAI.QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.QuadraticInitialBound
theorem _root_.solution
    {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset α) (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hg : ∀ i, lambda ∉ Q i) (hc : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, rowCoprimeMask P S z * finiteSexticRow Q hg j z *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ S.card * (pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖) := by
  rw [canonical_masked_radial_dilations P hinj S Q hcop hg j W M hM]
  calc
    _ ≤ ∑ E ∈ S.powerset, ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        finiteSexticRow Q hg j (primeSubsetGenerator P E) *
        ∑' z : O, finiteSexticRow Q hg j z *
          W (‖eisEmbedding z‖ ^ 2 / (M / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _E ∈ S.powerset, pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖ := by
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul, norm_mul]
      have hp := canonical_polya_vinogradov Q hcop hg hc j hj0 hj6 W _
        (primeSubset_reducedScale_pos P E hM)
      have hmul : ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ‖finiteSexticRow Q hg j (primeSubsetGenerator P E)‖ ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (norm_ideal_moebius_le_one _)
            (finiteSexticRow_norm_le_one Q hg j _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul _
      exact (mul_le_of_le_one_left (norm_nonneg _) hmul).trans hp
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
end OAI.QuadraticInitialBound
