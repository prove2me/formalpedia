-- Prove2me | solution 1 for OAI.GaussGeneratorTransport.moebius_squarefreePairPoissonKernel_conversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:20:27.339424+00:00
-- url     : https://prove2.me/submissions/4a088687-43bd-4a17-a972-ce9a42fa23b2

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_MixedGaussConversion_moebius_mixed_gauss_conversion
import Theorems.Thm_OAI_GaussGeneratorTransport_pair_moebius_eq_active
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_GaussGeneratorTransport_squarefreePairPoissonKernel_eq_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open MixedGaussConversion
namespace OAI.GaussGeneratorTransport
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ)) *
      squarefreePairPoissonKernel (fun i => Ideal.span {p i}) hinj hgood S T W scale =
      convertedPairPoissonKernel p hp hgood S T W scale := by
  let q : activeSupport S T → O := fun i => p i.val
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  have hg : (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
      canonicalProductGauss q (fun i => hp i.val) hQ (fun i => hgood i.val)
        (activeExponent S T) = activeConvertedGauss p hp hgood S T := by
    have he : activeExponent S T =
        (fun i : activeSupport S T => if decide (i.val ∈ S \ T) then 5 else 1) := by
      funext i
      simp only [activeExponent, decide_eq_true_eq]
    unfold activeConvertedGauss
    rw [he]
    exact moebius_mixed_gauss_conversion q (fun i => hp i.val) hQ (fun i => hgood i.val)
      (fun i => hchar i.val) (fun i => hprimary i.val) (fun i => decide (i.val ∈ S \ T))
  rw [pair_moebius_eq_active p hinj S T, squarefreePairPoissonKernel_eq_product p hp hinj hgood]
  change (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
      (((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ
        (fun i => hgood i.val) (activeExponent S T) / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
          activePairDualSeries p hgood S T W scale) = _
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
        ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
          canonicalProductGauss q (fun i => hp i.val) hQ (fun i => hgood i.val)
            (activeExponent S T)) * activePairDualSeries p hgood S T W scale := by ring
    _ = _ := by rw [hg]; rfl
end OAI.GaussGeneratorTransport
