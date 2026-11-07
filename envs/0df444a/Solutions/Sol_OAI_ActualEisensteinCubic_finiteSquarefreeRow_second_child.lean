-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finiteSquarefreeRow_second_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:00:52.860041+00:00
-- url     : https://prove2.me/submissions/7e5625c5-0e95-4ee7-abef-da12e1c2ab27

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_mul
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_conj_as_row_label
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
open scoped ComplexConjugate
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι)
    (d e k J C v : O) :
    star (finiteSquarefreeRow P hgood S e) *
      finiteSquarefreeRow P hgood S d *
      finiteSquarefreeRow P hgood S k *
      (finiteSquarefreeRow P hgood S (J * C)) ^ 4 *
      (finiteSquarefreeRow P hgood S v) ^ 4 =
    finiteSquarefreeRow P hgood S (d * e * k) *
      (finiteSquarefreeRow P hgood S (J * C * e * v)) ^ 4 := by
  rw [finiteSquarefreeRow_conj_as_row_label P hgood S e]
  simp only [finiteSquarefreeRow_mul]
  ring
end OAI.ActualEisensteinCubic
