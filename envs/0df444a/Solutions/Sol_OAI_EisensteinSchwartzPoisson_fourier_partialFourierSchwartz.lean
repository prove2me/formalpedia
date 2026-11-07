-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.fourier_partialFourierSchwartz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:22:08.106196+00:00
-- url     : https://prove2.me/submissions/0d45975f-9435-41e7-ba99-34fac03242ca

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_fourier_partialFourier
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_partialFourierSchwartz_coe

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
theorem _root_.solution (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourierSchwartz f η : ℝ → ℂ) ξ =
      𝓕 (f : ℂ → ℂ) ((ξ : ℂ) + Complex.I * (η : ℂ)) := by
  rw [partialFourierSchwartz_coe, fourier_partialFourier, complexPoint_eq]
end OAI.EisensteinSchwartzPoisson
