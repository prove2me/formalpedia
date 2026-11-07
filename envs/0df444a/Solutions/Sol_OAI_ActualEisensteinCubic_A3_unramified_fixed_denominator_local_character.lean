-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.A3_unramified_fixed_denominator_local_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:30.237277+00:00
-- url     : https://prove2.me/submissions/aad23bda-e8ac-4d22-9ded-51f1e3eda6cd

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftCusp_A3_unramified_det_relation
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
open OAI.ActualEisensteinCubic
open ShortDraftCusp
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b c d : O) (hdet : a * d - b * c = 1)
    (hd : d ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P (-b)) *
      cubicChar P hgood (Ideal.Quotient.mk P c) = 1 := by
  have hd0 : Ideal.Quotient.mk P d = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hd
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_unramified_det_relation a b c d hdet)
  simp only [map_mul, map_sub, map_one, hd0, mul_zero, sub_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_one] using hh
end OAI.ActualEisensteinCubic
