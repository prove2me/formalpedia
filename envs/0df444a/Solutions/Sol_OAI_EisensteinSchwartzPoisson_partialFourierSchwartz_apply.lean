-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.partialFourierSchwartz_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:00:31.35336+00:00
-- url     : https://prove2.me/submissions/e56686d7-224e-4494-bece-f609a6e7381b

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_partialFourier_continuous
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_partialFourier_integrable
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_fourier_partialFourier

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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourierSchwartz f η x = partialFourier f η x := by
  have heq : 𝓕 (partialFourier f η) =
      (horizontalSlice (𝓕 f) η : ℝ → ℂ) := by
    funext ξ
    rw [fourier_partialFourier, horizontalSlice_apply]
    exact (congrFun (SchwartzMap.fourier_coe f) (complexPoint ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier f η)) := by
    rw [heq]
    exact (horizontalSlice (𝓕 f) η).integrable
  change (𝓕⁻ (horizontalSlice (𝓕 f) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice (𝓕 f) η)) x, ← heq]
  exact (partialFourier_integrable f η).fourierInv_fourier_eq hi
    (partialFourier_continuous f η).continuousAt
end OAI.EisensteinSchwartzPoisson
