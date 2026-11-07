-- Prove2me | solution 1 for OAI.FiniteSFactor.outsideExpSum_restore_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:44:20.547973+00:00
-- url     : https://prove2.me/submissions/66643e85-60f5-4b4d-acb8-589488adca46

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_FiniteSFactor_outsideCoeff_exp_summable_baseChange
import Theorems.Thm_OAI_ConcretePrimeRowBridge_baseChangeWeight_zero_of_not_squarefree
import Theorems.Thm_OAI_FiniteSFactor_outsideExpSum_restore_insert_prime
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeWeight_mul_of_isRelPrime
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeWeight_zero_of_not_squarefree


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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open OAI.FiniteSFactor
namespace OAI.FiniteSFactor
theorem _root_.solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (t : ℝ) (ht : 0 < t) :
    outsideExpSum S (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      outsideExpSum (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          outsideExpSum (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm P : ℝ) * t) := by
  have hN : (0 : ℝ) < (Ideal.absNorm P : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  exact outsideExpSum_restore_insert_prime S hS P hP hPnot
    (ShortDraftHeckeBridge.baseChangeWeight χ)
    (ShortDraftHeckeBridge.baseChangeWeight_zero_of_not_squarefree χ)
    (ShortDraftHeckeBridge.baseChangeWeight_mul_of_isRelPrime χ)
    t
    (outsideCoeff_exp_summable_baseChange χ (insert P S) t ht)
    (outsideCoeff_exp_summable_baseChange χ (insert P S)
      ((Ideal.absNorm P : ℝ) * t) (mul_pos hN ht))
end OAI.FiniteSFactor
