-- Prove2me | solution 1 for OAI.CubicReflectionKernel.paperKernel_euler_uniform_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:15:16.714894+00:00
-- url     : https://prove2.me/submissions/adc9793e-57f6-4a5f-91a4-77617e85f8a2

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_InverseContour
import Theorems.Thm_OAI_CubicReflectionKernel_paperKernel_euler_power_decay
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
import Theorems.Thm_OAI_LocalLogFourier_euler_two_regime_bound
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
open OAI.CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace OAI.CubicReflectionKernel
theorem _root_.solution
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel V) i x‖ ≤ C := by
  choose c hc hb using fun i : Fin (K + 1) =>
    paperKernel_euler_power_decay V a b ha hsupp hV A i.val
  let D : ℝ := (∑ i : Fin (K + 1), c i) + 1
  have hD : 0 < D := by
    have hs : (0 : ℝ) ≤ ∑ i : Fin (K + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hci (i : Fin (K + 1)) : c i ≤ D := by
    have hs : c i ≤ ∑ k : Fin (K + 1), c k :=
      Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
    dsimp [D]
    linarith
  have hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖LocalLogFourier.eulerDeriv (paperKernel V) i x‖ ≤ D := by
    intro i hi x hx hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hp : x ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    calc
      _ ≤ c k * x ^ (1 / 4 : ℝ) := (hb k x hx).1
      _ ≤ c k := by simpa using mul_le_mul_of_nonneg_left hp (hc k).le
      _ ≤ D := hci k
  have hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel V) i x‖ ≤ D := by
    intro i hi x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hxpow : x ^ A ≠ 0 := pow_ne_zero A hx.ne'
    calc
      _ ≤ x ^ A * (c k * x ^ (-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left (hb k x hx).2 (pow_nonneg hx.le A)
      _ = c k := by
        rw [Real.rpow_neg hx.le, Real.rpow_natCast]
        field_simp
      _ ≤ D := hci k
  refine ⟨2 ^ A * (D + D), by positivity, ?_⟩
  intro i hi x hx
  exact LocalLogFourier.euler_two_regime_bound (paperKernel V) A K D D hD.le hD.le
    hsmall hlarge i hi x hx
end OAI.CubicReflectionKernel
