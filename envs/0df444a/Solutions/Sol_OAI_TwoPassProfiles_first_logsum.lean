-- Prove2me | solution 1 for OAI.TwoPassProfiles.first_logsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:54:20.824073+00:00
-- url     : https://prove2.me/submissions/3194060d-cf66-403b-83b1-2c91e0acad3c

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
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
open OAI.TwoPassProfiles
namespace OAI.TwoPassProfiles
theorem _root_.solution
    (K y d f E t c x₁ x₂ : ℝ) :
    (∑ j : Fin 9, firstCoeff j * firstLogs K y d f E t c x₁ x₂ j) =
      Real.log K + Real.log y - Real.log d -
      2 * Real.log f - Real.log E - 2 * Real.log t -
      Real.log c - Real.log x₁ - Real.log x₂ := by
  simp [Fin.sum_univ_succ, firstCoeff, firstLogs]
  ring
end OAI.TwoPassProfiles
