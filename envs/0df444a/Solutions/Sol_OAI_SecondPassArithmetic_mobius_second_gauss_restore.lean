-- Prove2me | solution 1 for OAI.SecondPassArithmetic.mobius_second_gauss_restore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:22:42.448046+00:00
-- url     : https://prove2.me/submissions/18aec5c5-70d5-4969-9920-15e1e182b2cb

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstPassage
import Theorems.Thm_OAI_SecondPassArithmetic_convertedColumnBlock_restore
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_pair_activeSupport
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstCauchyArithmetic_active_productGauss_eq_mobius_converted
import Theorems.Thm_OAI_FirstCauchyArithmetic_star_supportMobius
import Theorems.Thm_OAI_FirstCauchyArithmetic_supportMobius_sq
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_MixedCrossSeparation_activeConvertedGauss_eq_columnBlocks
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_false
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_true
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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG convertedColumnBlock quadraticCrossPhase
  columnPrimeCoprime columnCoefficient_cancel_false columnCoefficient_cancel_true)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
namespace OAI.SecondPassArithmetic
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T)
    (C₁ C₂ : Finset ι → ℂ) (e k : O) :
    star (supportMobius (fun i => Ideal.span {p i}) S * C₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * C₂ T) *
      activeGaussRowFactor p hp hinj hg T S e k =
    quadraticCrossPhase p hg T S * star (secondColumnMinus p hp hcop hg C₁ e k S) *
      secondColumnPlus p hp hcop hg C₂ e k T := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hmS := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj S
  have hmT := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj T
  have hr (u : O) :
      finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) u =
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T u) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u := by
    have hh := finiteSquarefreeRow_pair_activeSupport (fun i => Ideal.span {p i}) hg T S u
    simpa [Finset.disjoint_iff_inter_eq_empty.mp hd.symm, rowCoprimeMask] using hh.symm
  unfold activeGaussRowFactor
  dsimp only
  rw [FirstCauchyArithmetic.active_productGauss_eq_mobius_converted p hp hinj hg hc hpr,
    MixedCrossSeparation.activeConvertedGauss_eq_columnBlocks p hp hg hpr T S,
    Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.sdiff_eq_self_of_disjoint hd,
    (convertedColumnBlock_restore p hp hcop hg hc hpr S).1,
    (convertedColumnBlock_restore p hp hcop hg hc hpr T).2, hr e, hr k]
  simp only [secondColumnMinus, secondColumnPlus, star_mul, star_star,
    FirstCauchyArithmetic.star_supportMobius]
  calc
    _ = (supportMobius (fun i => Ideal.span {p i}) S * supportMobius (fun i => Ideal.span {p i}) S) *
      (supportMobius (fun i => Ideal.span {p i}) T * supportMobius (fun i => Ideal.span {p i}) T) *
      (quadraticCrossPhase p hg T S *
        (star (columnCoefficient p hp hcop hg S) * columnG p hp hcop hg S * star (C₁ S) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k)) *
        (columnCoefficient p hp hcop hg T * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T (-1) *
          star (columnG p hp hcop hg T) * C₂ T * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T e) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T k)) := by ring
    _ = _ := by rw [hmS, hmT]; ring
end OAI.SecondPassArithmetic
