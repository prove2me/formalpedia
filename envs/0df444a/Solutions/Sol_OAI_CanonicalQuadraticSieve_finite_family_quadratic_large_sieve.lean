-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.finite_family_quadratic_large_sieve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:58:03.858056+00:00
-- url     : https://prove2.me/submissions/3d4adaa2-1aee-4bc8-82f1-b95343cadb6b

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_sharp
import Theorems.Thm_OAI_CanonicalQuadraticSieve_energy_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_family_squared_norm_le
import Theorems.Thm_OAI_FiniteSieveOperator_energy_bound


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
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ (M N : ℝ), 1≤M → 1≤N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → Ideal O) (cols : n → Ideal O),
      Function.Injective rows → Function.Injective cols →
      (∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i):ℝ)≤M) →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
    ∀ a : n → ℂ,
      (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i))*a j‖^2) ≤
        C*(M*N)^ε*(M+N)*∑j,‖a j‖^2 := by
  intro ε hε
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  classical
  have he := FiniteSieveOperator.energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) a
  have hn := family_squared_norm_le rows cols hr hc M N hrows hcols
  have hE : 0≤∑j,‖a j‖^2 := by positivity
  exact he.trans ((mul_le_mul_of_nonneg_right hn hE).trans
    (mul_le_mul_of_nonneg_right (hsharp M N hM hN) hE))
end OAI.CanonicalQuadraticSieve
