-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberCoeff_eq_pairAF_prime_pow_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:40.55675+00:00
-- url     : https://prove2.me/submissions/a2ad9e3c-fb99-4242-be76-a9807d646864

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pairAF_prime_pow_ge_three
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_baseChangeWeight_prime_pow_ge_three

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
theorem _root_.solution {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k) :
    normFiberCoeff (baseChangeWeight χ) (p ^ k) =
      pairAF χ (baseChangeChar χ) (p ^ k) := by
  rw [normFiberCoeff_baseChangeWeight_prime_pow_ge_three χ hp hk,
    pairAF_prime_pow_ge_three χ (baseChangeChar χ) hp hk]
end OAI.ShortDraftHeckeBridge
