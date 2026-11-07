-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.paperRadialFourier_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:30:05.615198+00:00
-- url     : https://prove2.me/submissions/49af4060-f5af-4799-af13-f31547ff3bc0

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_eq_plane
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFrequency_sqrt_norm_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply



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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (W : 𝓢(ℝ, ℂ)) (A : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ A * ‖paperRadialFourier W t‖ ≤
      (2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * A) *
        (Finset.Iic (2 * A, 0)).sup (schwartzSeminormFamily ℝ ℂ ℂ)
          (radialFourierCLM W) := by
  let ξ : ℂ := paperFrequency (Real.sqrt t : ℂ)
  have hn : ‖ξ‖ ^ 2 = (4 / 3 : ℝ) * t := paperFrequency_sqrt_norm_sq t ht
  have hscale : 0 ≤ (2 / Real.sqrt 3 : ℝ) := by positivity
  have hpow : (1 + t) ^ A ≤ (1 + ‖ξ‖) ^ (2 * A) := by
    have hbase : 1 + t ≤ (1 + ‖ξ‖) ^ 2 := by
      nlinarith [norm_nonneg ξ]
    calc
      (1 + t) ^ A ≤ ((1 + ‖ξ‖) ^ 2) ^ A := pow_le_pow_left₀ (by positivity) hbase A
      _ = _ := by rw [← pow_mul]
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2 * A, 0)) (k := 2 * A) (n := 0) le_rfl le_rfl (radialFourierCLM W) ξ
  simp only [norm_iteratedFDeriv_zero] at hb
  rw [paperRadialFourier_eq_plane, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  change (1 + t) ^ A * ((2 / Real.sqrt 3) * ‖radialFourierCLM W ξ‖) ≤ _
  calc
    _ = (2 / Real.sqrt 3) * ((1 + t) ^ A * ‖radialFourierCLM W ξ‖) := by ring
    _ ≤ (2 / Real.sqrt 3) * ((1 + ‖ξ‖) ^ (2 * A) * ‖radialFourierCLM W ξ‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hscale
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hb hscale using 1 <;> first | rfl | (ring_nf; rfl)
end OAI.EisensteinSchwartzPoisson
