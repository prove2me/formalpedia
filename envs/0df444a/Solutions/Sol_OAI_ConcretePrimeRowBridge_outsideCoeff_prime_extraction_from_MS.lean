-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.outsideCoeff_prime_extraction_from_MS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:24:54.956808+00:00
-- url     : https://prove2.me/submissions/b38d1872-8d23-410d-904f-f64614f1c2a9

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Theorems.Thm_OAI_ConcretePrimeRowBridge_baseChange_prime_extraction_from_MS
import Theorems.Thm_OAI_ConcretePrimeRowBridge_outsideIdealsUpTo_norm_le
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
open OAI.ConcretePrimeRowBridge
open ShortDraftHeckeBridge FiniteSFactor
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n * W n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  let F := outsideIdealsUpTo S D
  have hbound := baseChange_prime_extraction_from_MS χ W F
    (outsideIdealsUpTo_ne_bot S D)
    (outsideIdealsUpTo_good S D hSbad)
    hW selected p D H ε hD hε
    (outsideIdealsUpTo_norm_le S D)
    hp hprime hinj hnormlower hnormupper hH hcount hmean
  simpa only [F, outsideIdealSum_eq_outsideCoeff_sum] using hbound
end OAI.ConcretePrimeRowBridge
