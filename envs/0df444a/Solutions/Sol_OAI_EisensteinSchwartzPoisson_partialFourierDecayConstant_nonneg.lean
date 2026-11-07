-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.partialFourierDecayConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:01:08.763004+00:00
-- url     : https://prove2.me/submissions/c61ddb9f-208a-4c65-a557-6e46abcd47d5

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_planeDecayConstant_nonneg

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
theorem _root_.solution (f : SchwartzMap ℂ ℂ) :
    0 ≤ partialFourierDecayConstant f :=
  mul_nonneg Real.pi_pos.le
    (add_nonneg (planeDecayConstant_nonneg _) (planeDecayConstant_nonneg _))
end OAI.EisensteinSchwartzPoisson
