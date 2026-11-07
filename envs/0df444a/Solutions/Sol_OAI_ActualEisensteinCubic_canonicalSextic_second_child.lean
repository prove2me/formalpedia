-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonicalSextic_second_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:00:03.476751+00:00
-- url     : https://prove2.me/submissions/f2a31f72-5f4f-4bc0-a9da-15f2a81387dc

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_conj_as_row_label
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
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (d e k J C v : O) :
    star (canonicalSextic P hgood (Ideal.Quotient.mk P e)) *
      canonicalSextic P hgood (Ideal.Quotient.mk P d) *
      canonicalSextic P hgood (Ideal.Quotient.mk P k) *
      (canonicalSextic P hgood (Ideal.Quotient.mk P (J * C))) ^ 4 *
      (canonicalSextic P hgood (Ideal.Quotient.mk P v)) ^ 4 =
    canonicalSextic P hgood (Ideal.Quotient.mk P (d * e * k)) *
      (canonicalSextic P hgood (Ideal.Quotient.mk P (J * C * e * v))) ^ 4 := by
  rw [canonicalSextic_conj_as_row_label P hgood e]
  simp only [map_mul]
  ring
end OAI.ActualEisensteinCubic
