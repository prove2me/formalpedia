-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.baseChange_restore_insert_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:34.444432+00:00
-- url     : https://prove2.me/submissions/41649393-9a97-48a1-b4fb-900465d618fc

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_FiniteSFactor_restore_insert_prime
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeWeight_zero_of_not_squarefree
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeWeight_mul_of_isRelPrime

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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution {q : ℕ}
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S) (n : ℕ) :
    FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n =
      FiniteSFactor.outsideCoeff (insert P S) (baseChangeWeight χ) n +
      (if Ideal.absNorm P ∣ n then
        baseChangeWeight χ P *
          FiniteSFactor.outsideCoeff (insert P S) (baseChangeWeight χ)
            (n / Ideal.absNorm P) else 0) := by
  exact FiniteSFactor.restore_insert_prime S hS P hP hPnot
    (baseChangeWeight χ) (baseChangeWeight_zero_of_not_squarefree χ)
    (baseChangeWeight_mul_of_isRelPrime χ) n
end OAI.ShortDraftHeckeBridge
