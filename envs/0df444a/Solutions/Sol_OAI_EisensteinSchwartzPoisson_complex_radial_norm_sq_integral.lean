-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.complex_radial_norm_sq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:53:36.353803+00:00
-- url     : https://prove2.me/submissions/e321876b-a6b7-43bf-aad7-a8914535fa3e

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory MeasureTheory.Measure Set Real
open scoped SchwartzMap FourierTransform
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (F : ℝ → ℂ) :
    (∫ z : ℂ, F (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, F t := by
  have hsub : (∫ r : ℝ in Ioi 0, (2 * r) • F (r ^ 2)) = ∫ t : ℝ in Ioi 0, F t := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
      using (integral_comp_rpow_Ioi_of_pos (g := F) (by norm_num : (0 : ℝ) < 2))
  have hsub' : (2 : ℂ) * (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) =
      ∫ t : ℝ in Ioi 0, F t := by
    simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
      mul_assoc, integral_const_mul] using hsub
  calc
    _ = ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 : ℂ) * F (p.1 ^ 2) := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp only [Complex.norm_polarCoord_symm, sq_abs, Complex.real_smul]
    _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) *
        ∫ _θ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
      rw [← setIntegral_prod_mul, volume_eq_prod]
      simp only [mul_one]
    _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) * (2 * Real.pi : ℂ) := by
      congr 1
      simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ,
        Set.univ_inter, volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]),
        sub_neg_eq_add, Complex.real_smul, mul_one]
      push_cast
      ring
    _ = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, F t := by rw [← hsub']; ring
end OAI.EisensteinSchwartzPoisson
