-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalDescentWeight_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:15:22.002236+00:00
-- url     : https://prove2.me/submissions/8d570572-0fd0-4d08-b1d0-b950aa6b70b2

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicVolume
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_UniformTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRowScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinFirstCoefficient_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinTriples_label_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
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
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinRadial_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalBin_complete_cost
import Theorems.Thm_OAI_SecondPassArithmetic_globalBin_mass_balance
import Theorems.Thm_OAI_SecondPassArithmetic_globalBin_triple_count
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledColumnScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledLabelScale_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_secondRayCoefficient_mass
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
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
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply



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
open OAI.SecondPassArithmetic
open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (C ε θ₁ θ₂ K ell B F : ℝ) (A J : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (side : Bool) (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q *
        (globalPooledColumnScale ell j*globalPooledLabelScale j)) ≤
    (C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*(globalBinLossScale B j)^ε /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A) *
      (128^3*(Real.exp 1)^18*(512*32^2))*((ell*B^3)*F) := by
  let Mchild := globalPooledColumnScale ell j*globalPooledLabelScale j
  let D := C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*(globalBinLossScale B j)^ε /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A
  have hmass : 0 < Mchild := mul_pos (globalPooledColumnScale_pos ell hell j)
    (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))
  have hY := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hR := globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell hY j
  have hfirst := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hL : 0 < globalPooledLabelScale j := zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)
  have h0 := (globalLogRep_pos j 0).le
  have h1 := (globalLogRep_pos j 1).le
  have h2 := (globalLogRep_pos j 2).le
  have h3 := (globalLogRep_pos j 3).le
  have h4 := (globalLogRep_pos j 4).le
  have hD : 0 ≤ D := by unfold D globalBinLossScale;positivity
  have hcount : ((globalBinTriples p s side j).card : ℝ) ≤ 128^3*(Real.exp 1)^3*globalBinTripleRange B j := by
    apply globalBin_triple_count p hp B hB side (globalLogSector p s side j) j
    · intro x hx;exact (Finset.mem_filter.mp hx).2
    · intro x hx;exact hk x (Finset.mem_filter.mp hx).1
    · intro x hx;exact hb₁ x (Finset.mem_filter.mp hx).1
    · intro x hx;exact hb₂ x (Finset.mem_filter.mp hx).1
  have hterm (ray : SecondRayIndex) :
      (∑ q∈globalBinTriples p s side j,globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q*Mchild) ≤
      D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*‖secondRayCoefficient ray‖ := by
    have ho : 0 ≤ globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j := by
      unfold globalPooledOuterBound;positivity
    calc
      _ ≤ ∑ q∈globalBinTriples p s side j,
          D*globalBinFirstCoefficient K ell B F j*globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j*Mchild^2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hloss : (globalPooledLabelScale j*Ideal.absNorm q.1)^ε ≤ (globalBinLossScale B j)^ε :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left
            (globalBinTriples_label_bound p hp B hB side s j hk hb₁ hb₂ q hq) hL.le) hε.le
        unfold globalDescentWeight D
        calc
          _ ≤ C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*globalBinFirstCoefficient K ell B F j *
              globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
              (globalBinLossScale B j)^ε /(1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A *Mchild*Mchild := by
                gcongr
          _ = _ := by ring
      _ = ((globalBinTriples p s side j).card : ℝ)*
          (D*globalBinFirstCoefficient K ell B F j*globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j*Mchild^2) := by simp
      _ ≤ (128^3*(Real.exp 1)^3*globalBinTripleRange B j)*
          (D*globalBinFirstCoefficient K ell B F j*globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j*Mchild^2) := by
        gcongr
      _ = D*(globalBinChildCharge B F j*Mchild)*‖secondRayCoefficient ray‖ := by
        have hc := globalBin_complete_cost K ell B F hK hell hB hF j ray
        change globalBinFirstCoefficient K ell B F j * _ * Mchild * _ = _ at hc
        calc
          _ = D*(globalBinFirstCoefficient K ell B F j *
              globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *Mchild *
              (128^3*(Real.exp 1)^3*globalBinTripleRange B j))*Mchild := by ring
          _ = _ := by rw [hc];ring
      _ = _ := by rw [show globalBinChildCharge B F j*Mchild=128^3*(Real.exp 1)^18*((ell*B^3)*F) from globalBin_mass_balance ell B F hB hF j]
  calc
    _ ≤ ∑ ray : SecondRayIndex,D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*‖secondRayCoefficient ray‖ :=
      Finset.sum_le_sum (fun ray _ => hterm ray)
    _ = D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*(∑ ray : SecondRayIndex,‖secondRayCoefficient ray‖) := by rw [Finset.mul_sum]
    _ ≤ D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*(512*32^2) := by
      apply mul_le_mul_of_nonneg_left secondRayCoefficient_mass
      positivity
    _ = _ := by dsimp only [D];ring
end OAI.SecondPassArithmetic
