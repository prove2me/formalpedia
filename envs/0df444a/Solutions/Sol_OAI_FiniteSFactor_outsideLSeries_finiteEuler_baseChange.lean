-- Prove2me | solution 1 for OAI.FiniteSFactor.outsideLSeries_finiteEuler_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:45:33.44082+00:00
-- url     : https://prove2.me/submissions/72731f9c-8ba7-448e-8910-2937580f1ddd

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_FiniteSFactor_outsideLSeries_restore_baseChange
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
    (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (∏ P ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s))) *
      LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert P S hPnot ih =>
      have hSP : ∀ Q ∈ S, Prime Q := by
        intro Q hQ
        exact hS Q (Finset.mem_insert_of_mem hQ)
      have hPP : Prime P := hS P (Finset.mem_insert_self P S)
      have hrest := outsideLSeries_restore_baseChange χ S hSP P hPP hPnot s hs
      calc
        LSeries (outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
            (∏ Q ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ Q *
              (Ideal.absNorm Q : ℂ) ^ (-s))) *
            LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s :=
          ih hSP
        _ = (∏ Q ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ Q *
              (Ideal.absNorm Q : ℂ) ^ (-s))) *
            ((1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
              (Ideal.absNorm P : ℂ) ^ (-s)) *
              LSeries (outsideCoeff (insert P S)
                (ShortDraftHeckeBridge.baseChangeWeight χ)) s) := by rw [hrest]
        _ = (∏ Q ∈ insert P S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ Q *
              (Ideal.absNorm Q : ℂ) ^ (-s))) *
            LSeries (outsideCoeff (insert P S)
              (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
          rw [Finset.prod_insert hPnot]
          ring
end OAI.FiniteSFactor
