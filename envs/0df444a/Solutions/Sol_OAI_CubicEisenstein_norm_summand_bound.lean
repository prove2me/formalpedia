-- Prove2me | solution 1 for OAI.CubicEisenstein.norm_summand_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:03:07.749191+00:00
-- url     : https://prove2.me/submissions/ef088eb3-03a1-4e76-b1fd-204c3a36852d

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayCoefficients
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_Rows
import Theorems.Thm_OAI_CubicEisenstein_embeddedRow_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_rowEnergy_pos
import Theorems.Thm_OAI_CubicEisenstein_rowOperator_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_rowBound_pos
import Theorems.Thm_OAI_CubicEisenstein_coordinates_le_transformed_energy
import Theorems.Thm_OAI_CubicEisenstein_norm_coordinates_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_norm_summand
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
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
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open scoped BigOperators Classical MatrixGroups
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
namespace OAI.CubicEisenstein
theorem _root_.solution (g : SL(2,ℂ)) (s : ℂ) (hs : 0 < s.re) (x : CuspCosets) :
    ‖summand g s x‖ ≤ (rowBound g) ^ (2*s.re) *
      ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re)) := by
  rw [norm_summand]
  have hn := norm_coordinates_ne_zero x
  have hb := rowBound_pos g
  have he := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  have hbd := coordinates_le_transformed_energy g (cosetRow x)
  change ‖rowCoordinates (cosetRow x)‖ ≤ rowBound g *
    Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) at hbd
  have hle : (‖rowCoordinates (cosetRow x)‖ / rowBound g) ^ 2 ≤
      rowEnergy (rowOperator g (embeddedRow x)) := by
    have hd : ‖rowCoordinates (cosetRow x)‖ / rowBound g ≤
        Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) :=
      (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hbd)
    have hsq := Real.sq_sqrt he.le
    nlinarith [div_pos hn hb, Real.sqrt_nonneg (rowEnergy (rowOperator g (embeddedRow x)))]
  have hp := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (div_pos hn hb)) hle (by linarith : -s.re ≤ 0)
  convert hp using 1
  rw [← Real.rpow_natCast_mul (div_nonneg hn.le hb.le) 2 (-s.re),
    Real.div_rpow hn.le hb.le]
  simp only [Nat.cast_ofNat, mul_neg, Real.rpow_neg hb.le, div_eq_mul_inv, inv_inv]
  exact mul_comm _ _
end OAI.CubicEisenstein
