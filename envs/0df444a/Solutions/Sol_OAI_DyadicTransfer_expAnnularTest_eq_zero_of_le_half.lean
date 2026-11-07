-- Prove2me | solution 1 for OAI.DyadicTransfer.expAnnularTest_eq_zero_of_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:03.013212+00:00
-- url     : https://prove2.me/submissions/7c14854b-1d79-4047-9f1e-dade42c2fe92

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_DyadicTransfer_annularCutoff_eq_zero_of_le_half
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
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (D : ℝ) (k : ℕ) {y : ℝ} (hy : y ≤ 1 / 2) :
    expAnnularTest φ D k y = 0 := by
  simp [expAnnularTest, annularCutoff_eq_zero_of_le_half φ hsmall hy]
end OAI.DyadicTransfer
