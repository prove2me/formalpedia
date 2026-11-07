-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberCoeff_eq_pairInverseCoeff_of_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:19:59.728313+00:00
-- url     : https://prove2.me/submissions/b40859e9-5466-4be4-a7fa-5a41493518ab

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_eq_pairAF_prime_pow_ge_three
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChange_normFiber_isMultiplicative
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiber_eq_pair_of_prime_powers
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pairAF_mult
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
theorem _root_.solution
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hprime : ∀ p : ℕ, p.Prime →
      normFiberCoeff (baseChangeWeight χ) p = pairAF χ (baseChangeChar χ) p)
    (hprimeSq : ∀ p : ℕ, p.Prime →
      normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
        pairAF χ (baseChangeChar χ) (p ^ 2))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff (baseChangeWeight χ) n =
      pairInverseCoeff χ (baseChangeChar χ) n := by
  apply normFiber_eq_pair_of_prime_powers χ (baseChangeChar χ)
    (baseChangeWeight χ) (baseChange_normFiber_isMultiplicative χ) ?_ n hn
  intro p k hp
  by_cases hk0 : k = 0
  · simpa [hk0] using
      (baseChange_normFiber_isMultiplicative χ).map_one.trans
        ((pairAF_mult χ (baseChangeChar χ)).map_one).symm
  by_cases hk1 : k = 1
  · simpa [hk1, toArithmeticFunction, hp.ne_zero] using hprime p hp
  by_cases hk2 : k = 2
  · simpa [hk2, toArithmeticFunction, hp.ne_zero] using hprimeSq p hp
  have hk3 : 3 ≤ k := by omega
  change (if p ^ k = 0 then (0 : ℂ) else
    normFiberCoeff (baseChangeWeight χ) (p ^ k)) = _
  rw [if_neg (pow_ne_zero k hp.ne_zero)]
  exact normFiberCoeff_eq_pairAF_prime_pow_ge_three χ hp hk3
end OAI.ShortDraftHeckeBridge
