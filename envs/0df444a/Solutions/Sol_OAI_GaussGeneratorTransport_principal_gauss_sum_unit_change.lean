-- Prove2me | solution 1 for OAI.GaussGeneratorTransport.principal_gauss_sum_unit_change
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:12:55.935742+00:00
-- url     : https://prove2.me/submissions/2ca9f0dc-4845-4986-9a86-3da4f8858070

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSexticRow_mul
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_eisTraceModChar_eq_paperE
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk



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
open OAI.GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
namespace OAI.GaussGeneratorTransport
theorem _root_.solution {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n)
    [Fintype (O ⧸ Ideal.span {c})] [Fintype (O ⧸ Ideal.span {n})] :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) =
      finiteSexticRow P hgood j (u : O) *
        ∑ r : O ⧸ Ideal.span {n}, principalSexticRow P hcop hgood j n hn r *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0 r := by
  let e₀ := Ideal.quotEquivOfEq (hn.trans hc.symm)
  let ū : (O ⧸ Ideal.span {n})ˣ := Units.map (Ideal.Quotient.mk (Ideal.span {n})).toMonoidHom u
  let e : (O ⧸ Ideal.span {n}) ≃ (O ⧸ Ideal.span {c}) := ū.mulLeft.trans e₀.toEquiv
  have he (a : O) : e (Ideal.Quotient.mk (Ideal.span {n}) a) =
      Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a) := by
    change e₀ (Ideal.Quotient.mk (Ideal.span {n}) (u : O) *
      Ideal.Quotient.mk (Ideal.span {n}) a) = _
    rw [← map_mul, Ideal.quotEquivOfEq_mk]
  rw [← Equiv.sum_comp e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [he, principalSexticRow_mk, principalSexticRow_mk, finiteSexticRow_mul]
  have hphase : eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
      (Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a)) =
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0
        (Ideal.Quotient.mk (Ideal.span {n}) a) := by
    rw [eisTraceModChar_eq_paperE, eisTraceModChar_eq_paperE, hcn, map_mul, map_mul]
    congr 1
    field_simp [eisEmbedding_ne_zero u.ne_zero]
  rw [hphase]
  ring
end OAI.GaussGeneratorTransport
