-- Prove2me | solution 1 for OAI.CubicReflectionKernel.paperKernel_euler_source_uniform_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:16:04.291108+00:00
-- url     : https://prove2.me/submissions/035cc378-67d3-4ea2-b55f-cbe84b1dfa98

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_InverseContour
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Theorems.Thm_OAI_CubicReflectionKernel_paperKernel_euler_source_power_decay
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
    (a b : ℝ) (ha : 0 < a) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ i ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose s c hc hb using fun i : Fin (K + 1) => paperKernel_euler_source_power_decay a b ha A i.val
  let S : Finset (ℕ × ℕ) := Finset.univ.biUnion s
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
  refine ⟨S, 2 ^ A * (D + D), by positivity, ?_⟩
  intro W hsupp
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsource (i : Fin (K + 1)) : c i * (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ D * Q := by
    have hsub : s i ⊆ S := Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hq : (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
      Seminorm.le_def.mp (Finset.sup_mono hsub) W
    exact mul_le_mul (hci i) hq (by positivity) hD.le
  have hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤ D * Q := by
    intro i hi x hx hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hp : x ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    calc
      _ ≤ (c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (1 / 4 : ℝ) := (hb k W hsupp x hx).1
      _ ≤ c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        simpa using mul_le_mul_of_nonneg_left hp (mul_nonneg (hc k).le (by positivity))
      _ ≤ D * Q := hsource k
  have hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤ D * Q := by
    intro i hi x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hxpow : x ^ A ≠ 0 := pow_ne_zero A hx.ne'
    calc
      _ ≤ x ^ A * ((c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left (hb k W hsupp x hx).2 (pow_nonneg hx.le A)
      _ = c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        rw [Real.rpow_neg hx.le, Real.rpow_natCast]
        field_simp
      _ ≤ D * Q := hsource k
  intro i hi x hx
  have hh := LocalLogFourier.euler_two_regime_bound (paperKernel W) A K (D * Q) (D * Q)
    (mul_nonneg hD.le hQ) (mul_nonneg hD.le hQ) hsmall hlarge i hi x hx
  convert hh using 1 ; dsimp [Q] ; ring
end OAI.CubicReflectionKernel
