-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.HasSieveExponent.actual_principal_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:05:00.634794+00:00
-- url     : https://prove2.me/submissions/04fbe811-7b56-48a5-98de-08badb794f7a

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspIntegration
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MaskedPrincipalBounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_reverse
import Theorems.Thm_OAI_CanonicalQuadraticSieve_actualPrincipalDifference_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sqrt_div_mul_rpow
import Theorems.Thm_OAI_IdealCoprimeSieveOperator_supportConstant_pos


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
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic IdealMobiusDivisorSum IdealCoprimeSieveOperator
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (cols : n → Ideal O) (_hinj : Function.Injective cols)
      (M N K : ℝ), 1 ≤ M → 1 ≤ N → 1 ≤ K →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      (∀ j k, columnRay (cols j) = columnRay (cols k)) →
      ∀ (a : n → ℂ) (G : Ideal O), Squarefree G →
      (∀ P ∈ fixedBadPrimes, P ∣ G) → ∀ (ε : ℝ) (hε : 0 < ε),
      ‖(Real.sqrt M : ℂ) * actualPrincipalDifference cols a G K‖ ≤
        ((idealDivisors G).card : ℝ)^2 * (supportConstant ε hε * N^ε) *
          C * (K*N)^deltaLoss * (Real.sqrt (M/K)*N + Real.sqrt M*K^(α-1/2)) *
          ∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hbound⟩ := hexp.reverse deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro n _ _ cols hinj M N K hM hN hK hcols hray a G hG hbad ε hε
  have hM0 : 0 ≤ M := by linarith
  have hK0 : 0 < K := by linarith
  have hs := actualPrincipalDifference_bound cols hinj N (by linarith) hcols hray a G hG hbad K hK0 ε hε
  have hsupp := (supportConstant_pos ε hε).le
  have hb := hbound K N hK hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg M)]
  calc
    _ ≤ Real.sqrt M * (((idealDivisors G).card : ℝ)^2 *
        ((1/Real.sqrt K)*sieveNorm K N*(supportConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt M * (((idealDivisors G).card : ℝ)^2 *
        ((1/Real.sqrt K)*(C*(K*N)^deltaLoss*(N+K^α))*(supportConstant ε hε*N^ε)*∑ j, ‖a j‖^2)) := by
      gcongr
    _ = ((idealDivisors G).card : ℝ)^2*(supportConstant ε hε*N^ε)*C*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*(N+K^α))*∑ j, ‖a j‖^2 := by
      rw [Real.sqrt_div hM0]
      ring
    _ = _ := by
      rw [mul_add, sqrt_div_mul_rpow M K α hM0 hK0]
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
