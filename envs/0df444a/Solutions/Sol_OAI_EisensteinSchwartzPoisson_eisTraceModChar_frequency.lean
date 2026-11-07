-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.eisTraceModChar_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:05:13.429367+00:00
-- url     : https://prove2.me/submissions/4b1a7337-060b-405e-9bcf-dd550cb1d1f0

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_eisTraceModChar_eq_paperE
import Theorems.Thm_OAI_GaussianShiftedPartition_representative_spec


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
theorem _root_.solution (c : O) (hc : c ≠ 0)
    (h : O) (r : O ⧸ Ideal.span {c}) :
    eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
      (Ideal.Quotient.mk (Ideal.span {c}) h * r) =
      paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
        eisEmbedding h / eisEmbedding c) := by
  conv_lhs => rw [← GaussianShiftedPartition.representative_spec c r, ← map_mul]
  rw [eisTraceModChar_eq_paperE, map_mul]
  congr 1
  ring
end OAI.EisensteinSchwartzPoisson
