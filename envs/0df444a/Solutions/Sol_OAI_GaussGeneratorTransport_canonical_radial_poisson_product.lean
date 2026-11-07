-- Prove2me | solution 1 for OAI.GaussGeneratorTransport.canonical_radial_poisson_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:32:03.864195+00:00
-- url     : https://prove2.me/submissions/db50bc17-49ef-4af6-9875-1e56f7d2017a

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Theorems.Thm_OAI_GaussGeneratorTransport_gauss_weighted_radial_sum_transport
import Theorems.Thm_OAI_GaussGeneratorTransport_finitePrimeModulus_norm_eq_product
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_radial_poisson_normalized
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
namespace OAI.GaussGeneratorTransport
theorem _root_.solution {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, finiteSexticRow (fun i => Ideal.span {p i}) hgood j z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalProductGauss p hp hcop hgood j /
        (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, p i)‖ ^ 2) := by
  have h := canonical_radial_poisson_normalized (fun i => Ideal.span {p i})
    hcop hgood hchar j hj0 hj6 W scale hscale
  dsimp only at h
  rw [finitePrimeModulus_norm_eq_product p] at h
  rw [h]
  have ht := gauss_weighted_radial_sum_transport p hp hcop hgood j
    (fun t => paperRadialFourier W (scale * t / ‖eisEmbedding (∏ i, p i)‖ ^ 2))
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
          ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
            paperRadialFourier W
              (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, p i)‖ ^ 2)) := by ring
    _ = _ := by rw [ht]; ring
end OAI.GaussGeneratorTransport
