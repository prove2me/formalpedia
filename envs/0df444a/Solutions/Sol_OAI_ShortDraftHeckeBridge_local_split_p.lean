-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.local_split_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:55:53.594955+00:00
-- url     : https://prove2.me/submissions/36f8085c-7ff7-4c12-8f33-7c502ca2e102

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_split_count_of_mod_one
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_p_fiber_split
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
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) p = -(2 : ℂ) * χ p := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) p
  have hcard : hf.toFinset.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p} hf]
    rw [norm_p_fiber_split hp hmod]
    exact split_count_of_mod_one hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) p =
      ∑ I ∈ hf.toFinset, -χ p := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = p := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime p).2 hp))
    rw [baseChangeWeight_prime χ I hprime, hnorm]
  rw [hsum]
  simp [hcard]
end OAI.ShortDraftHeckeBridge
