-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.local_inert_p_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:55:49.950925+00:00
-- url     : https://prove2.me/submissions/1dcd7511-bd3c-400a-b81e-c509863c97aa

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_inert_count_of_mod_two
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_p_sq_fiber_inert
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeWeight_prime
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = -χ (p ^ 2) := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p ^ 2} hf]
    rw [norm_p_sq_fiber_inert hp hmod]
    exact inert_count_of_mod_two hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
      ∑ I ∈ hf.toFinset, -χ (p ^ 2) := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hover : I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
      rw [← norm_p_sq_fiber_inert hp hmod]
      exact hf.mem_toFinset.mp hI
    have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hI
    let : I.IsPrime := hover.1
    have hprime : Prime I := Ideal.prime_of_isPrime (by
      intro hbot
      have : Ideal.absNorm I = 0 := by rw [hbot]; simp
      rw [hnorm] at this
      exact (pow_ne_zero 2 hp.ne_zero) this) inferInstance
    simpa only [hnorm, Nat.cast_pow] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]
end OAI.ShortDraftHeckeBridge
