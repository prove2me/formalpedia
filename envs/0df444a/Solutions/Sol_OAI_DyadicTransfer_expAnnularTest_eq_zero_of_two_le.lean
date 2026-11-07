-- Prove2me | solution 1 for OAI.DyadicTransfer.expAnnularTest_eq_zero_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:03.579437+00:00
-- url     : https://prove2.me/submissions/b7446bea-0c84-45d5-9179-e05fcd80b82c

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_DyadicTransfer_annularCutoff_eq_zero_of_two_le
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
open OAI.DyadicTransfer
namespace OAI.DyadicTransfer
theorem _root_.solution (φ : ℝ → ℂ)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (D : ℝ) (k : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    expAnnularTest φ D k y = 0 := by
  simp [expAnnularTest, annularCutoff_eq_zero_of_two_le φ hlarge hy]
end OAI.DyadicTransfer
