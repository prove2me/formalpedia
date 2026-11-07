-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.pairAF_prime_pow_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:08.75696+00:00
-- url     : https://prove2.me/submissions/75675187-233d-459a-9247-abed2c741932

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftHeckeBridge_invCharAF_apply
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
namespace ShortDraftHeckeBridge
private theorem invCharAF_prime_pow_ge_two {q : ℕ}
    (χ : DirichletCharacter ℂ q) {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    invCharAF χ (p ^ j) = 0 := by
  rw [invCharAF_apply χ (pow_ne_zero j hp.ne_zero),
    ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
  simp [show j ≠ 1 by omega]
end ShortDraftHeckeBridge
namespace NormSplitArithmetic
end NormSplitArithmetic
namespace NormFiberCRT
end NormFiberCRT
namespace NormFiberMult
end NormFiberMult
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
open Filter Asymptotics
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    pairAF χ ψ (p ^ k) = 0 := by
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i ≤ k := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  have hdiv : p ^ k / p ^ i = p ^ (k - i) := by
    have heq : k - i + i = k := Nat.sub_add_cancel hik
    calc
      p ^ k / p ^ i = (p ^ (k - i) * p ^ i) / p ^ i := by rw [← pow_add, heq]
      _ = p ^ (k - i) := by simp [hp.ne_zero]
  rw [hdiv]
  by_cases hii : 2 ≤ i
  · rw [invCharAF_prime_pow_ge_two χ hp hii, zero_mul]
  · have hki : 2 ≤ k - i := by omega
    rw [invCharAF_prime_pow_ge_two ψ hp hki, mul_zero]
end OAI.ShortDraftHeckeBridge
