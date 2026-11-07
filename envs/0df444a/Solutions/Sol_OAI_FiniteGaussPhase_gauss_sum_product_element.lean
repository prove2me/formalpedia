-- Prove2me | solution 1 for OAI.FiniteGaussPhase.gauss_sum_product_element
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:12:44.826238+00:00
-- url     : https://prove2.me/submissions/5a06dd0b-5aff-4802-8ea1-bfbbb08ea496

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Theorems.Thm_OAI_IdealGaussCRT_gauss_sum_finite_crt
import Theorems.Thm_OAI_FiniteGaussPhase_cofactor_coprime
import Theorems.Thm_OAI_FiniteGaussPhase_coordinate_trace_character
import Theorems.Thm_OAI_IdealGaussCRT_bezout_of_principal_coprime
import Theorems.Thm_OAI_IdealGaussCRT_gauss_shift_bezout_left


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
open scoped BigOperators Classical
open OAI.FiniteGaussPhase
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.FiniteGaussPhase
theorem _root_.solution {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    [Fintype (O ⧸ Ideal.span {∏ i, p i})] [∀ i, Fintype (O ⧸ Ideal.span {p i})]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    (∑ x : O ⧸ Ideal.span {∏ i, p i},
      (∏ i, χ i (productElementCRT p hcop x i)) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) x) =
      ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)) *
        gaussSum (χ i) (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i)) := by
  rw [IdealGaussCRT.gauss_sum_finite_crt]
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨u, v, hbez⟩ := IdealGaussCRT.bezout_of_principal_coprime (cofactor_coprime p hcop i)
  rw [coordinate_trace_character p hp hcop i u v hbez]
  exact IdealGaussCRT.gauss_shift_bezout_left hbez (χ i) _
end OAI.FiniteGaussPhase
