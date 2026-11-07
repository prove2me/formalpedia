-- Prove2me | solution 1 for OAI.FirstCauchyArithmetic.a_weighted_converted_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:34:36.582892+00:00
-- url     : https://prove2.me/submissions/393955ad-c219-4b02-b1b8-e7f223cd8937

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_false
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_true
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstCauchyArithmetic_star_supportMobius
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_MixedCrossSeparation_activeConvertedGauss_eq_columnBlocks
import Theorems.Thm_OAI_MixedCrossSeparation_active_dual_row_factorization
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.FirstCauchyArithmetic
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open MixedCrossSeparation GaussGeneratorTransport ConcretePrimeRowBridge EisensteinSchwartzPoisson
namespace OAI.FirstCauchyArithmetic
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (hd : Disjoint S T) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
    star (columnCoefficient p hp hcop hg S * C₁ S) *
      (columnCoefficient p hp hcop hg T * C₂ T) *
      (supportMobius P S * supportMobius P T * activeConvertedGauss p hp hg S T) *
        (row d * star (row h)) =
    quadraticCrossPhase p hg S T *
      star (supportMobius P S * firstPassColumnMinus p hp hcop hg C₁ d S *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * firstPassColumnPlus p hp hcop hg C₂ d T *
        star (finiteSquarefreeRow P hg T h)) := by
  dsimp only
  rw [activeConvertedGauss_eq_columnBlocks p hp hg hpr S T,
    active_dual_row_factorization (fun i => Ideal.span {p i}) hg S T d h,
    Finset.sdiff_eq_self_of_disjoint hd, Finset.sdiff_eq_self_of_disjoint hd.symm]
  have hminus := columnCoefficient_cancel_true p hp hcop hg hc hpr S
  have hplus := columnCoefficient_cancel_false p hp hcop hg hc hpr T
  simp only [firstPassColumnMinus, firstPassColumnPlus, star_mul, star_star,
    star_supportMobius]
  calc
    _ = (star (columnCoefficient p hp hcop hg S) * convertedColumnBlock p hp hg S true) *
      (columnCoefficient p hp hcop hg T * convertedColumnBlock p hp hg T false) *
      (star (C₁ S) * C₂ T * supportMobius (fun i => Ideal.span {p i}) S *
        supportMobius (fun i => Ideal.span {p i}) T * quadraticCrossPhase p hg S T *
        (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d)) *
        (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T d *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T h))) := by ring
    _ = _ := by rw [hminus, hplus]; ring
end OAI.FirstCauchyArithmetic
