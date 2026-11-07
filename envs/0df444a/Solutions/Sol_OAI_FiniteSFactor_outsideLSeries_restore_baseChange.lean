-- Prove2me | solution 1 for OAI.FiniteSFactor.outsideLSeries_restore_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:44:08.606286+00:00
-- url     : https://prove2.me/submissions/d94cc571-548e-4c99-8f27-1be7c9e9e95e

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_FiniteSFactor_outsideCoeff_LSeriesSummable_baseChange
import Theorems.Thm_OAI_ConcretePrimeRowBridge_baseChangeWeight_zero_of_not_squarefree
import Theorems.Thm_OAI_FiniteEulerRestoration_tsum_restore_one_prime
import Theorems.Thm_OAI_FiniteSFactor_restore_insert_prime
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeWeight_mul_of_isRelPrime
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeWeight_zero_of_not_squarefree
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace FiniteSFactor
private theorem term_eq_mul_kernel (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term a s n = a n * dirichletKernel s n := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, dirichletKernel]
  · simp [LSeries.term, dirichletKernel, hn, div_eq_mul_inv, Complex.cpow_neg]
private theorem kernel_shift {N : ℕ} (hN : 0 < N) (s : ℂ) (m : ℕ) :
    dirichletKernel s (N * m) =
      (N : ℂ) ^ (-s) * dirichletKernel s m := by
  by_cases hm : m = 0
  · subst m
    simp [dirichletKernel]
  · have hNm : N * m ≠ 0 := mul_ne_zero hN.ne' hm
    simp only [dirichletKernel, if_neg hNm, if_neg hm]
    simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow N m (-s)
private theorem tsum_mul_kernel_eq_LSeries (a : ℕ → ℂ) (s : ℂ) :
    (∑' n : ℕ, a n * dirichletKernel s n) = LSeries a s := by
  unfold LSeries
  apply tsum_congr
  intro n
  exact (term_eq_mul_kernel a s n).symm
end FiniteSFactor
open Filter
namespace CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge
end CompactScaleBridge
end
end OAI
end

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
open OAI.FiniteSFactor
namespace OAI.FiniteSFactor
theorem _root_.solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s)) *
        LSeries (outsideCoeff (insert P S)
          (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  let N : ℕ := Ideal.absNorm P
  let a : ℕ → ℂ := outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)
  let b : ℕ → ℂ := outsideCoeff (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ)
  let c : ℂ := ShortDraftHeckeBridge.baseChangeWeight χ P
  have hN : 0 < N :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  have hcoeff (n : ℕ) :
      a n = b n + if N ∣ n then c * b (n / N) else 0 :=
    restore_insert_prime S hS P hP hPnot
      (ShortDraftHeckeBridge.baseChangeWeight χ)
      (ShortDraftHeckeBridge.baseChangeWeight_zero_of_not_squarefree χ)
      (ShortDraftHeckeBridge.baseChangeWeight_mul_of_isRelPrime χ) n
  have hbsum : LSeriesSummable b s :=
    outsideCoeff_LSeriesSummable_baseChange χ (insert P S) s hs
  change Summable (LSeries.term b s) at hbsum
  have hb : Summable (fun n : ℕ => b n * dirichletKernel s n) := by
    simpa only [← term_eq_mul_kernel b s] using hbsum
  have hshiftPoint (m : ℕ) :
      b m * dirichletKernel s (N * m) =
        (N : ℂ) ^ (-s) * LSeries.term b s m := by
    rw [kernel_shift hN s m, term_eq_mul_kernel]
    ring
  have hshift : Summable (fun m : ℕ => b m * dirichletKernel s (N * m)) := by
    simpa only [hshiftPoint] using hbsum.mul_left ((N : ℂ) ^ (-s))
  have hgeneric := FiniteEulerRestoration.tsum_restore_one_prime hN c a b
    (dirichletKernel s) hcoeff hb hshift
  rw [tsum_mul_kernel_eq_LSeries a s, tsum_mul_kernel_eq_LSeries b s] at hgeneric
  have hshiftSum :
      (∑' m : ℕ, b m * dirichletKernel s (N * m)) =
        (N : ℂ) ^ (-s) * LSeries b s := by
    calc
      (∑' m : ℕ, b m * dirichletKernel s (N * m)) =
          ∑' m : ℕ, (N : ℂ) ^ (-s) * LSeries.term b s m := by
            apply tsum_congr
            exact hshiftPoint
      _ = (N : ℂ) ^ (-s) * LSeries b s := by
            rw [tsum_mul_left]
            rfl
  rw [hshiftSum] at hgeneric
  change LSeries a s = (1 + c * (N : ℂ) ^ (-s)) * LSeries b s
  calc
    LSeries a s = LSeries b s + c * ((N : ℂ) ^ (-s) * LSeries b s) := hgeneric
    _ = (1 + c * (N : ℂ) ^ (-s)) * LSeries b s := by ring
end OAI.FiniteSFactor
