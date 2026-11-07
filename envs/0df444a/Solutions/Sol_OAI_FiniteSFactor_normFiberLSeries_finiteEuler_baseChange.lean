-- Prove2me | solution 1 for OAI.FiniteSFactor.normFiberLSeries_finiteEuler_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:47:06.817315+00:00
-- url     : https://prove2.me/submissions/71aad4de-fdc0-4f06-bc19-1349f5a0fea0

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_FiniteSFactor_outsideLSeries_finiteEuler_baseChange
import Theorems.Thm_OAI_FiniteSFactor_outsideCoeff_empty_eq_normFiberCoeff
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeWeight_prime


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
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (ShortDraftHeckeBridge.normFiberCoeff
      (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (∏ P ∈ S, (1 - χ (Ideal.absNorm P) *
        (Ideal.absNorm P : ℂ) ^ (-s))) *
      LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  have h := outsideLSeries_finiteEuler_baseChange χ S hS s hs
  have hfun : outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ) =
      ShortDraftHeckeBridge.normFiberCoeff
        (ShortDraftHeckeBridge.baseChangeWeight χ) := by
    funext n
    exact outsideCoeff_empty_eq_normFiberCoeff _ n
  rw [hfun] at h
  have hprod :
      (∏ P ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s))) =
      (∏ P ∈ S, (1 - χ (Ideal.absNorm P) *
        (Ideal.absNorm P : ℂ) ^ (-s))) := by
    apply Finset.prod_congr rfl
    intro P hPS
    rw [ShortDraftHeckeBridge.baseChangeWeight_prime χ P (hS P hPS)]
    ring
  rw [hprod] at h
  exact h
end OAI.FiniteSFactor
