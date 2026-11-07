-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.scaled_cauchy_int_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:14:27.307695+00:00
-- url     : https://prove2.me/submissions/f214b200-88e8-44c0-8257-2023e23c0492

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_scaled_cauchy_nat_bound
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_summable_scaled_cauchy_nat
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply



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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open OAI.EisensteinSchwartzPoisson
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (b : ℝ) (hb : 0 < b) :
    (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / b := by
  have hs := summable_scaled_cauchy_nat b hb
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have hneg : Summable (fun n : ℕ =>
      (1 + (b * ((-(n + 1) : ℤ) : ℝ)) ^ 2)⁻¹) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one, mul_neg, neg_sq] using hs1
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹)
    (by simpa only [Int.cast_natCast] using hs) hneg]
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one, mul_neg,
    neg_sq]
  have hz := hs.tsum_eq_zero_add
  have he : (∑' n : ℕ, (1 + (b * (↑n + 1)) ^ 2)⁻¹) =
      (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hz.symm
  rw [he]
  have := scaled_cauchy_nat_bound b hb
  have hh : Real.pi / (2 * b) = (Real.pi / b) / 2 := by ring
  rw [hh] at this
  linarith
end OAI.EisensteinSchwartzPoisson
