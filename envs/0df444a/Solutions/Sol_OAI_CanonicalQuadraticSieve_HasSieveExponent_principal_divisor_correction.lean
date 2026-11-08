-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.HasSieveExponent.principal_divisor_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:20:52.288345+00:00
-- url     : https://prove2.me/submissions/30335548-c268-40f6-997a-f598f6c53bc9

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedDefects
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_GlobalEncoding
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_large_principal_pool
import Theorems.Thm_OAI_CanonicalQuadraticSieve_largePrincipalProductAt_le_window
import Theorems.Thm_OAI_CanonicalQuadraticSieve_principalDivisorCorrection_le_product
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnDivisorPool_norm_bounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_mem_columnDivisorPool_of_dvd


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
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm d:ℝ)) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  let pairCols : n × p → Ideal O := fun x => left x.1*right x.2
  let K := columnDivisorPool pairCols
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hp0 : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hl0 x.1) (hr0 x.2)
  have hk : ∀ j k d, d ∣ left j*right k → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hp0 (j,k) d hd
  calc
    _ ≤ largePrincipalProductAt K rows left right a b M P :=
      principalDivisorCorrection_le_product K rows left right a b M P hl0 hr0 hk
    _ ≤ largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) :=
      largePrincipalProductAt_le_window K S T rows left right a b M P hl0 hr0
        (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
    _ ≤ _ := hexp.large_principal_pool deltaLoss hδ ε hε S T B N M V hB hN hM hV
      (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2))
      (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2))
      rows left right hr hl hri hrows hleft hright a b _
      (fun D _ E _ i hp => hP (D*E) i hp.2)
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
