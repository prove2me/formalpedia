-- Prove2me | solution 1 for OAI.CompletedGauss.ideal_cube_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:10.4661+00:00
-- url     : https://prove2.me/submissions/ad0d679a-0aae-4cc6-acb8-fa2ac0301992

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Theorems.Thm_OAI_CompletedGauss_mulFiber_moebius_sum
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
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
open OAI.CompletedGauss
open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)
namespace OAI.CompletedGauss
theorem _root_.solution (c : Ideal O →* ℂ) (hc0 : c 0 = 0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2))).Finite) :
    (∑' H : Ideal O, ∑' J : Ideal O,
      (UniqueFactorizationMonoid.moebius H : ℂ) * c (H * J) * f (H * J)) = f 1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2)
  have hF : Summable F := summable_of_hasFiniteSupport hfinite
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.val) =
      if B = 1 then f 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have heach : ∀ p : MulFiber 0, F p.val = 0 := by
        intro p
        dsimp [F]
        rw [p.property, hc0, mul_zero, zero_mul]
      simp only [heach, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = ∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) * (c B * f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property, mul_assoc]
        _ = (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) * (c B * f B) := by
          rw [tsum_mul_right]
        _ = if B = 1 then f 1 else 0 := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with h
          · subst B; simp only [map_one, one_mul]
          · simp
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.val) (∑' p, F p) at hs
  simp_rw [hfiber] at hs
  have hsum : (∑' p, F p) = f 1 := by
    have he := hs.tsum_eq.symm
    simpa only [tsum_ite_eq, one_ne_zero] using he
  rw [← hF.tsum_prod]
  exact hsum
end OAI.CompletedGauss
