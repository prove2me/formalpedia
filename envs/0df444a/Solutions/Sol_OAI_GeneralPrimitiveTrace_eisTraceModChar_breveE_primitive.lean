-- Prove2me | solution 1 for OAI.GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:12:00.016189+00:00
-- url     : https://prove2.me/submissions/34a9cd16-9541-460b-8d9a-80a7f1bbb2ea

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Theorems.Thm_OAI_GeneralPrimitiveTrace_in_coordinate_lattice_of_two_phases
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
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
open OAI.GeneralPrimitiveTrace
open Complex EisensteinEmbedding ConcreteTraceCRT
open scoped ComplexConjugate
namespace OAI.GeneralPrimitiveTrace
theorem _root_.solution (c : ActualEisensteinCubic.O) (hc : c ≠ 0) :
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc).IsPrimitive := by
  intro a ha hshift
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  let z : ℂ := eisEmbedding x / eisEmbedding c
  have hci : eisEmbedding c ≠ 0 := eisEmbedding_ne_zero hc
  have hbase : ∀ y : ActualEisensteinCubic.O,
      ShortDraftTrace.breveE (eisEmbedding (x * y) / (eisEmbedding c * eisLam)) = 1 := by
    intro y
    have hp := congrArg (fun f : AddChar (ActualEisensteinCubic.O ⧸ Ideal.span {c}) ℂ =>
      f (Ideal.Quotient.mk (Ideal.span {c}) y)) hshift
    simpa only [AddChar.mulShift_apply, ← map_mul, eisTraceModChar,
      IdealGaussCRT.traceModChar_mk, AddChar.one_apply] using hp
  have h1 : ShortDraftTrace.breveE (z / eisLam) = 1 := by
    convert hbase 1 using 1
    simp only [mul_one]
    dsimp [z]
    ring_nf
  have hw : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1 := by
    convert hbase pb.gen using 1
    rw [map_mul, show eisEmbedding pb.gen = omega3 from embedding_gen omega3 omega3_sq]
    dsimp [z]
    ring_nf
  have hz := in_coordinate_lattice_of_two_phases z h1 hw
  obtain ⟨q, hq⟩ := toCoordinateSubring_surjective ⟨z, hz⟩
  have hiq : eisEmbedding q = z := congrArg Subtype.val hq
  have hcq : c * q = x := by
    apply eisEmbedding_injective
    rw [map_mul, hiq]
    dsimp [z]
    field_simp
  apply ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr ⟨q, hcq.symm⟩
end OAI.GeneralPrimitiveTrace
