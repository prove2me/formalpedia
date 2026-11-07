-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.two_regime_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:44:37.333543+00:00
-- url     : https://prove2.me/submissions/8b110e26-dc3a-45c0-89fd-ff73b5608e93

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles

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
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (A : ℕ) (f B₀ B₁ M N : ℝ)
    (_hf : 0 ≤ f) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hM : 0 < M) (hN : 0 < N)
    (hsmall : f ≤ B₀) (hlarge : N ≤ M → f ≤ B₁ * (N / M) ^ A) :
    f ≤ (2 : ℝ) ^ A * (B₀ + B₁) / (1 + M / N) ^ A := by
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + M / N) A)).mpr
  by_cases hMN : M ≤ N
  · have hratio : M / N ≤ 1 := (div_le_one hN).mpr hMN
    have hp : (1 + M / N) ^ A ≤ (2 : ℝ) ^ A :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ ≤ B₀ * (2 : ℝ) ^ A := mul_le_mul hsmall hp (by positivity) hB₀
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) A]
  · have hNM : N ≤ M := le_of_not_ge hMN
    have hratio : N / M ≤ 1 := (div_le_one hM).mpr hNM
    have hp : (1 + N / M) ^ A ≤ (2 : ℝ) ^ A :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have he : N / M * (1 + M / N) = 1 + N / M := by field_simp; ring
    calc
      _ ≤ (B₁ * (N / M) ^ A) * (1 + M / N) ^ A :=
        mul_le_mul_of_nonneg_right (hlarge hNM) (by positivity)
      _ = B₁ * (1 + N / M) ^ A := by rw [mul_assoc, ← mul_pow, he]
      _ ≤ B₁ * (2 : ℝ) ^ A := mul_le_mul_of_nonneg_left hp hB₁
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) A]
end OAI.EisensteinSchwartzPoisson
