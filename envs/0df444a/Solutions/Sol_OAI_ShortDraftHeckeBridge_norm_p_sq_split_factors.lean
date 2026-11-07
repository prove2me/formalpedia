-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.norm_p_sq_split_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:19.05784+00:00
-- url     : https://prove2.me/submissions/8c54d334-40ef-4468-8b16-28a6f6caee45

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_absNorm_split
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_prime_implies_over
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (I : Ideal O) (hI : Ideal.absNorm I = p ^ 2) :
    ∃ P Q : Ideal O,
      P ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      Q ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      I = P * Q := by
  have hdiv : p ∣ Ideal.absNorm I := by
    rw [hI]
    exact dvd_pow_self p (by decide)
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
  have : P.IsPrime := hPmax.isPrime
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  obtain ⟨Q, hIQ⟩ := hPdiv
  have hQN : Ideal.absNorm Q = p := by
    have heq := congrArg Ideal.absNorm hIQ
    simp only [map_mul] at heq
    rw [hI, hPN] at heq
    have hppos := hp.pos
    nlinarith
  exact ⟨P, Q, ⟨inferInstance, inferInstance⟩,
    norm_prime_implies_over hp Q hQN, hIQ⟩
end OAI.ShortDraftHeckeBridge
