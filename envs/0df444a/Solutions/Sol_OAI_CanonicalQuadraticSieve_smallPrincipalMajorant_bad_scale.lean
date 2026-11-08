-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.smallPrincipalMajorant_bad_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:17:46.989099+00:00
-- url     : https://prove2.me/submissions/64fb8918-781c-447a-8fd3-19346bdce63a

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicSectors
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalMajorants
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorEnergyFactor_mono_coefficients
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorEnergyFactor_nonneg
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorExponentConstant_pos
import Theorems.Thm_OAI_CanonicalQuadraticSieve_dual_bad_sector_scale


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U Q : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hQ : 1 ≤ Q)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    (1/Q)*smallPrincipalMajorant hexp deltaLoss hδ ε hε (B/Q) N (M*Q) F U a' b' ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have hQp : 0 < Q := by linarith
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' ha hb
  have hp : ((B/Q)*N)^deltaLoss ≤ (B*N)^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    exact mul_le_mul_of_nonneg_right (div_le_self hB hQ) hN
  have hs := dual_bad_sector_scale M F B Q U α hM hF hB hQ hU hα
  have he0 := divisorEnergyFactor_nonneg ε hε N a' b'
  have he1 := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold smallPrincipalMajorant
  calc
    _ = ((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a' b'*(divisorExponentConstant hexp deltaLoss hδ*((B/Q)*N)^deltaLoss)*
        ((1/Q)*(M*Q/F+(2*U)*Real.sqrt (M*Q/F)*(B/Q)^(α-1/2)))) := by ring
    _ ≤ _ := by gcongr
end OAI.CanonicalQuadraticSieve
