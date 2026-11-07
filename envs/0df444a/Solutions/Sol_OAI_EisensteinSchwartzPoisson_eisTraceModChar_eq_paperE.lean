-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.eisTraceModChar_eq_paperE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:03:50.316059+00:00
-- url     : https://prove2.me/submissions/c34b465e-b0f2-4f3e-bf49-cefd9f563134

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson

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
theorem _root_.solution (c : O) (hc : c ≠ 0) (z : O) :
    eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
      (Ideal.Quotient.mk (Ideal.span {c}) z) =
      paperE (eisEmbedding z / eisEmbedding c) := by
  rw [eisTraceModChar, IdealGaussCRT.traceModChar_mk]
  unfold paperE
  congr 1
  ring
end OAI.EisensteinSchwartzPoisson
