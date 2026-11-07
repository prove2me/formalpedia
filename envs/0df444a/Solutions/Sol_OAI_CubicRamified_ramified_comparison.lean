-- Prove2me | solution 1 for OAI.CubicRamified.ramified_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:54.915191+00:00
-- url     : https://prove2.me/submissions/5c9acaea-544f-4cdf-9256-c20ced011a91

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Theorems.Thm_OAI_CubicJacobiGlobal_idealSymbol_prime
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_reciprocity
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_congr
import Theorems.Thm_OAI_CubicRamified_cubicValue_ne_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_A3_cubicChar_neg_one
import Theorems.Thm_OAI_ActualEisensteinCubic_cubic_reciprocity_primary
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk



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
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical
open OAI.CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
namespace OAI.CubicRamified
theorem _root_.solution
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hqP : q ∉ P) (_hpQ : p ∉ Q)
    (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by
  have hp0 : p ≠ 0 := by
    intro hz
    apply (NeZero.ne P)
    simp [hP, hz]
  have hq0 : q ≠ 0 := by
    intro hz
    apply (NeZero.ne Q)
    simp [hQ, hz]
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hrP : r ∉ P := by
    intro hrP
    have hd : p - q ∈ P := by rw [hfactor]; exact P.mul_mem_left _ hrP
    have hmem := P.sub_mem hpP hd
    exact hqP (by convert hmem using 1 ; ring)
  have hrr : cubicChar P hgP (Ideal.Quotient.mk P r) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q r) := by
    have heq : symbol p r = symbol q r := symbol_congr
      (by rw [hfactor]; exact dvd_mul_left r _)
    have h := (symbol_reciprocity r p hr0 hp0 hr hp).trans
      (heq.trans (symbol_reciprocity q r hq0 hr0 hq hr))
    simpa only [symbol, ← hP, ← hQ, idealSymbol_prime _ hgP,
      idealSymbol_prime _ hgQ] using h
  have heq : cubicChar P hgP (Ideal.Quotient.mk P (p - q)) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q (p - q)) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hpP, zero_sub,
      neg_eq_neg_one_mul, map_mul, A3_cubicChar_neg_one P hgP, one_mul,
      map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hqQ, sub_zero]
    exact cubic_reciprocity_primary P Q hgP hgQ p q hP hQ hp hq
  simp only [hfactor, map_mul, map_pow] at heq
  rw [← hrr] at heq
  exact mul_right_cancel₀ (cubicValue_ne_zero P hgP r hrP) heq
end OAI.CubicRamified
