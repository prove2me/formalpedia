-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.local_ramified_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:55:49.493539+00:00
-- url     : https://prove2.me/submissions/4588ce25-2713-4035-859a-bb777de77468

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_ramified_count
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_three_fiber
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
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 3 = -χ 3 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 3
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = 3} hf]
    rw [norm_three_fiber]
    exact ramified_count
  have hsum : normFiberCoeff (baseChangeWeight χ) 3 =
      ∑ I ∈ hf.toFinset, -χ 3 := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = 3 := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime 3).2 (by decide)))
    simpa only [hnorm, Nat.cast_ofNat] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]
end OAI.ShortDraftHeckeBridge
