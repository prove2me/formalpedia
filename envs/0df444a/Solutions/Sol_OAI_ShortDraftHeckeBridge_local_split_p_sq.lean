-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.local_split_p_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:55:50.463124+00:00
-- url     : https://prove2.me/submissions/aa99c343-367d-4a4a-9728-09cbcf1cc054

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_split_count_of_mod_one
import Theorems.Thm_OAI_ShortDraftHeckeBridge_absNorm_split
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_p_sq_split_factors
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
end ShortDraftHeckeBridge
namespace ActualEisensteinCubic
open MulChar AddChar
end ActualEisensteinCubic
namespace ShortDraftHeckeBridge
private theorem baseChangeWeight_prime_sq_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ (P ^ 2) = 0 := by
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    have hunit : IsUnit P := hsq P (by rw [pow_two])
    exact hP.irreducible.not_isUnit hunit
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp
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
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = χ (p ^ 2) := by
  classical
  let s : Set (Ideal O) := (Ideal.span {(p : ℤ)}).primesOver O
  obtain ⟨P, Q, hPQ, hset⟩ := Set.ncard_eq_two.mp (split_count_of_mod_one hp hmod)
  have hPover : P ∈ s := by
    change P ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  have hQover : Q ∈ s := by
    change Q ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  let : P.IsPrime := hPover.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover.2
  let : Q.IsPrime := hQover.1
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQover.2
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  have hQN : Ideal.absNorm Q = p := absNorm_split hp hmod Q
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hPN
    exact hp.ne_zero hPN.symm
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hQN
    exact hp.ne_zero hQN.symm
  have hPprime : Prime P := Ideal.prime_of_isPrime hPne inferInstance
  have hQprime : Prime Q := Ideal.prime_of_isPrime hQne inferInstance
  have : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPne
  have : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQne
  have hrel : IsRelPrime P Q := (Ideal.isCoprime_of_isMaximal hPQ).isRelPrime
  have hmu : UniqueFactorizationMonoid.moebius (P * Q) = 1 := by
    rw [hrel.moebius_mul, hPprime.irreducible.moebius_eq,
      hQprime.irreducible.moebius_eq]
    norm_num
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hmem : P * Q ∈ hf.toFinset := by
    rw [hf.mem_toFinset]
    change Ideal.absNorm (P * Q) = p ^ 2
    rw [map_mul, hPN, hQN, pow_two]
  calc
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
        ∑ I ∈ hf.toFinset, baseChangeWeight χ I := by rfl
    _ = baseChangeWeight χ (P * Q) := by
      apply Finset.sum_eq_single (P * Q)
      · intro I hImem hneq
        have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hImem
        obtain ⟨A, B, hA, hB, rfl⟩ := norm_p_sq_split_factors hp hmod I hnorm
        rw [hset] at hA hB
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
        rcases hA with hAP | hAQ <;> rcases hB with hBP | hBQ
        · rw [hAP, hBP]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ P hPprime
        · exact False.elim (hneq (by rw [hAP, hBQ]))
        · exact False.elim (hneq (by rw [hAQ, hBP, mul_comm]))
        · rw [hAQ, hBQ]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ Q hQprime
      · intro hnot
        exact False.elim (hnot hmem)
    _ = χ (p ^ 2) := by
      rw [baseChangeWeight, hmu]
      have hnorm : Ideal.absNorm (P * Q) = p ^ 2 := by
        rw [map_mul, hPN, hQN, pow_two]
      simp [hnorm, Nat.cast_pow]
end OAI.ShortDraftHeckeBridge
