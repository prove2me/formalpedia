-- Prove2me | solution 1 for OAI.CompactScaleBridge.FixedTestPrimeMS.bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:44:04.121395+00:00
-- url     : https://prove2.me/submissions/12bdeac9-db1e-4629-99b1-7064b8b97e8b

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_CompactScaleBridge_fixedTestWeight_eq
import Theorems.Thm_OAI_ConcretePrimeRowBridge_outsideCoeff_prime_extraction_from_MS
import Theorems.Thm_OAI_ConcretePrimeRowBridge_outsideIdealSum_eq_outsideCoeff_sum
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
open Filter
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge
namespace OAI.CompactScaleBridge
namespace FixedTestPrimeMS
theorem _root_.solution
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε : ℝ)
    (h : FixedTestPrimeMS χ S hSbad W m ε)
    (hm : 0 < m) (hε : 0 ≤ ε) (hW : ∀ y : ℝ, ‖W y‖ ≤ 1) :
    ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ ≤
      384 * ((2 * m : ℕ) : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  have hWeight : ∀ n : ℕ, ‖fixedTestWeight W m n‖ ≤ 1 := by
    intro n
    exact hW _
  have hD : 1 ≤ 2 * m := by omega
  have hbound := outsideCoeff_prime_extraction_from_MS χ
    (fixedTestWeight W m) S hSbad hWeight h.selected (fun p : O => p)
    (2 * m) h.H ε hD hε h.hp h.hprime h.hinj h.hnormlower
    h.hnormupper h.hH h.hcount h.hmean
  rw [← outsideIdealSum_eq_outsideCoeff_sum] at hbound
  simpa only [fixedTestWeight_eq W hm] using hbound
end FixedTestPrimeMS
end OAI.CompactScaleBridge
