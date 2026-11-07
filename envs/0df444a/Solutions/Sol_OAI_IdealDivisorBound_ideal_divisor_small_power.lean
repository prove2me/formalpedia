-- Prove2me | solution 1 for OAI.IdealDivisorBound.ideal_divisor_small_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:19:09.099834+00:00
-- url     : https://prove2.me/submissions/275e6484-30ba-45b1-9186-2937151ab321

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Theorems.Thm_OAI_IdealDivisorBound_divisor_card_le_product
import Theorems.Thm_OAI_IdealDivisorBound_linear_le_geometric
import Theorems.Thm_OAI_IdealDivisorBound_support_norm_two_le
import Theorems.Thm_OAI_IdealDivisorBound_norm_factor_product
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
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
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
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
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



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
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum UniqueFactorizationMonoid
open OAI.IdealDivisorBound
namespace OAI.IdealDivisorBound
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      ((idealDivisors I).card : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  let b : ℝ := (2 : ℝ) ^ ε
  have hb : 1 < b := by
    dsimp [b]
    exact Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (b - 1)⁻¹
  have hc : 1 ≤ c := by
    dsimp [c]
    have hi : 0 ≤ (b - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hb.le)
    linarith
  refine ⟨c ^ small.card, by positivity, ?_⟩
  intro I hI
  let S := primeSupport I
  let e := fun P : Ideal O => (normalizedFactors I).count P
  have hfac (P : Ideal O) (hP : P ∈ S) :
      ((e P + 1 : ℕ) : ℝ) ≤
        (if P ∈ small then c else 1) * ((Ideal.absNorm P : ℝ) ^ ε) ^ e P := by
    have hnorm : (2 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast support_norm_two_le hP
    have hbase : b ≤ (Ideal.absNorm P : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) hnorm hε.le
    by_cases hp : P ∈ small
    · rw [if_pos hp]
      have hlin := linear_le_geometric b hb (e P)
      have hl : ((e P + 1 : ℕ) : ℝ) ≤ c * b ^ e P := by
        simpa only [Nat.cast_add, Nat.cast_one, c] using hlin
      apply hl.trans
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)
    · rw [if_neg hp, one_mul]
      have hn : N ≤ Ideal.absNorm P := by
        have : ¬ Ideal.absNorm P ≤ N := fun h => hp (by simpa [small] using h)
        omega
      have hp2 := hN _ hn
      calc
        _ ≤ (2 : ℝ) ^ e P := by
          have hh := one_add_mul_sub_le_pow (by norm_num : (-1 : ℝ) ≤ 2) (e P)
          norm_num at hh ⊢
          linarith
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp2 _
  have hprod := Finset.prod_le_prod
    (fun P (_ : P ∈ S) => (by positivity : (0 : ℝ) ≤ ((e P + 1 : ℕ) : ℝ))) hfac
  have hconst : (∏ P ∈ S, if P ∈ small then c else 1) ≤ c ^ small.card := by
    have he : (∏ P ∈ S, if P ∈ small then c else 1) = c ^ (S ∩ small).card := by
      simp []
    rw [he]
    exact pow_le_pow_right₀ hc (Finset.card_le_card Finset.inter_subset_right)
  have hpow : (∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ ε) ^ e P) =
      (Ideal.absNorm I : ℝ) ^ ε := by
    calc
      _ = ∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ e P) ^ ε := by
        apply Finset.prod_congr rfl
        intro P hP
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        rw [mul_comm]
      _ = (∏ P ∈ S, (Ideal.absNorm P : ℝ) ^ e P) ^ ε :=
        Real.finsetProd_rpow S _ (fun _ _ => by positivity) ε
      _ = _ := by rw [norm_factor_product I hI]
  have hcard : ((idealDivisors I).card : ℝ) ≤ ∏ P ∈ S, ((e P + 1 : ℕ) : ℝ) := by
    exact_mod_cast divisor_card_le_product I hI
  apply hcard.trans
  rw [Finset.prod_mul_distrib, hpow] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hconst (by positivity))
end OAI.IdealDivisorBound
