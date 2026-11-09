-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.hasSieveExponent_one_of_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T03:59:18.429416+00:00
-- url     : https://prove2.me/submissions/6e65898b-4610-4bcd-a869-78a3251797bf

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison

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
open scoped BigOperators
open OAI.CanonicalQuadraticSieve
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    (happrox : ∀ η : ℝ, 0<η → ∃ α : ℝ, α≤1+η ∧ HasSieveExponent α) :
    HasSieveExponent 1 := by
  intro ε hε
  have he : 0<ε/2 := by positivity
  obtain ⟨α,hα,h⟩ := happrox (ε/2) he
  obtain ⟨C,hC,hbound⟩ := h (ε/2) he
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0≤M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hNmn : N≤M*N := by nlinarith
  have hQ : 1≤(M*N)^(ε/2) := Real.one_le_rpow hMN he.le
  have hnα : N^α ≤ (M*N)^(ε/2)*N := by
    calc
      _ ≤ N^(1+ε/2) := Real.rpow_le_rpow_of_exponent_le hN hα
      _ = N*N^(ε/2) := by rw [Real.rpow_add hN0,Real.rpow_one]
      _ ≤ N*(M*N)^(ε/2) := by gcongr
      _ = _ := mul_comm _ _
  have hsum : M+N^α ≤ (M*N)^(ε/2)*(M+N) := by
    nlinarith [mul_le_mul_of_nonneg_right hQ hM0]
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^α) := hbound M N hM hN
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N)) := by gcongr
    _ = C*(M*N)^ε*(M+N^(1:ℝ)) := by
      rw [Real.rpow_one]
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add (by positivity : 0<M*N)]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N) := by ring
        _ = _ := by rw [hp]
end OAI.CanonicalQuadraticSieve
