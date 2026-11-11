-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalRetained_canonical_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:40:19.037696+00:00
-- url     : https://prove2.me/submissions/7303843b-139a-49bd-a57b-0961caf5d3f4

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_RetainedDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalTailBounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooled_mass_le_parent
import Theorems.Thm_OAI_SecondPassArithmetic_globalArithmeticTargets_nonzero
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
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
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_fixedDepthRank_initial
import Theorems.Thm_OAI_SecondPassArithmetic_fixedDepthRank_step
import Theorems.Thm_OAI_SecondPassArithmetic_globalArithmeticTargets_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalArithmeticTargets_squarefree
import Theorems.Thm_OAI_SecondPassArithmetic_globalBin_invariant_small_padding
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledColumnScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledDelta_ge
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledLabelScale_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRow_contraction
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooled_J_bound
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
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
attribute [local simp] OAI.InitialMeanSquare.initialLogProfile_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply



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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (source:Finset (GlobalSecondData ι)) (side:Bool) (q:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j:GlobalLogIndex)
    (hq:q∈globalBinTriples p source side j)
    (Z η Ksrc K ell B F:ℝ) (m:ActualEisensteinCubic.O)
    (hZ:1<Z) (hη:η≤(1:ℝ)/1000) (hKsrc:0<Ksrc) (hK:0<K) (hKle:K≤Ksrc)
    (hell:0<ell) (hB:0<B) (hF:1≤F) (hprogress:Z^((1:ℝ)/1000)≤B*F)
    (hlarge:Real.exp 4≤B*F) (hstart:Ksrc≤Z^3)
    (hk:∀x∈source,x.source.frequency≠0)
    (hb₁:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hretained:globalBinRadial ell (globalPooledRowScale K ell B F j) j≤Z^η):
    let X:=globalPooledColumnScale ell j
    let lengthScale:=globalPooledLabelScale j
    let Kchild:=globalLogRep j 8*Real.exp 1
    0<X ∧ 1≤lengthScale ∧ 1≤Kchild ∧ X*lengthScale≤(ell*B^3)*F ∧
      Kchild≤Ksrc/Z^((1:ℝ)/1000) ∧ fixedDepthRank Z Kchild+1≤fixedDepthRank Z Ksrc ∧
      fixedDepthRank Z Ksrc≤3000 ∧ Kchild*‖eisEmbedding (fixedTripleMask m q)‖^2/(X*lengthScale)≤
        Z^η*(K*‖eisEmbedding m‖^2/((ell*B^3)*F)) ∧
      (∀z∈globalArithmeticTargets p source side q j,
        Squarefree z.1 ∧ z.2≠0 ∧ (Ideal.absNorm z.1:ℝ)≤lengthScale ∧ ‖eisEmbedding z.2‖^2≤Kchild) := by
  obtain ⟨x,hx,hqx⟩:=Finset.mem_image.mp hq
  obtain ⟨hxs,hj⟩:=Finset.mem_filter.mp hx
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hJ:globalLogRep j 4≤B^2:=by
    simpa only [hj] using globalPooled_J_bound p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
  have hD:Z^η≤globalPooledDelta B F j:=
    (Real.rpow_le_rpow_of_exponent_le hZ.le hη).trans
      (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
  have hr:globalLogRep j 8*Real.exp 1≤K/globalPooledDelta B F j:=
    globalPooledRow_contraction K ell B F hK hell hB hF0 j hJ (hretained.trans hD)
  have hKchild:1≤globalLogRep j 8*Real.exp 1:=one_le_mul_of_one_le_of_one_le
    (globalLogRep_ge_one j 8) (Real.one_le_exp (by norm_num))
  have hsmall:globalLogRep j 8*Real.exp 1≤Ksrc/Z^((1:ℝ)/1000):=by
    apply hr.trans
    calc
      _ ≤ K/Z^((1:ℝ)/1000):=div_le_div_of_nonneg_left hK.le
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
        (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
      _ ≤ _:=div_le_div_of_nonneg_right hKle (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hinv:=globalBin_invariant_small_padding p hp Z η K ell B F hZ hK hell hB hF side x
    (hk x hxs) m (hb₁ x hxs) (hb₂ x hxs) (by simpa only [hj] using hretained)
  simp only [hj,hqx] at hinv
  refine ⟨globalPooledColumnScale_pos ell hell j,globalPooledLabelScale_ge_one j,hKchild,
    globalPooled_mass_le_parent K ell B F hell hB hF0 j hJ hlarge,hsmall,
    fixedDepthRank_step Z Ksrc _ hZ hKsrc hKchild hsmall,
    fixedDepthRank_initial Z Ksrc hZ hKsrc hstart,hinv,?_⟩
  intro z hz
  have hb:=globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨globalArithmeticTargets_squarefree p source side q j z hz,
    globalArithmeticTargets_nonzero p source side q j hk z hz,hb.2.1,hb.2.2⟩
end OAI.SecondPassArithmetic
