-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finiteSquarefreeRow_self_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:55:13.238507+00:00
-- url     : https://prove2.me/submissions/f990cd50-0c34-4e2b-9c56-54a77e3bdfb7

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S : Finset ι) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood S u =
      rowCoprimeMask P S u := by
  classical
  unfold finiteSquarefreeRow rowCoprimeMask
  rw [star_prod, ← Finset.prod_mul_distrib]
  by_cases h : ∃ i ∈ S, u ∈ P i
  · rw [if_pos h]
    obtain ⟨i, hi, hui⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hui, MulChar.map_zero]
    simp
  · rw [if_neg h]
    apply Finset.prod_eq_one
    intro i hi
    rw [MulChar.star_apply', ← MulChar.mul_apply, inv_mul_cancel]
    apply MulChar.one_apply
    let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
    exact isUnit_iff_ne_zero.mpr fun hui => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hui⟩
end OAI.ActualEisensteinCubic
