-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.fourierChar_paperFrequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:05:11.340838+00:00
-- url     : https://prove2.me/submissions/21c055f1-9e42-47c6-82a2-611c2840ccbf

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperE_eq_exp
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_inner_paperFrequency

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
open OAI.EisensteinSchwartzPoisson
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (z u : ℂ) :
    (Real.fourierChar (inner ℝ z (paperFrequency u)) : ℂ) = paperE (z * u) := by
  rw [inner_paperFrequency, paperE_eq_exp, Real.fourierChar_apply]
  congr 1
  push_cast
  ring
end OAI.EisensteinSchwartzPoisson
