-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:31.205223+00:00
-- url     : https://prove2.me/submissions/0217f08f-09a8-450e-8a76-90d3406b70ca

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_eq_pairAF_prime
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_eq_pairAF_prime_sq
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_eq_pairInverseCoeff_of_local

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
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff (baseChangeWeight χ) n =
      pairInverseCoeff χ (baseChangeChar χ) n := by
  exact normFiberCoeff_eq_pairInverseCoeff_of_local χ
    (fun p hp => normFiberCoeff_eq_pairAF_prime χ hp)
    (fun p hp => normFiberCoeff_eq_pairAF_prime_sq χ hp) n hn
end OAI.ShortDraftHeckeBridge
