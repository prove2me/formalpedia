-- Prove2me | solution 1 for OAI.CompactScaleBridge.outsideCoeff_compact_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:54:58.61221+00:00
-- url     : https://prove2.me/submissions/462e9189-72bc-4852-8c26-dbd525ef6663

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_CompactScaleBridge_outsideCoeff_baseChange_zero
import Theorems.Thm_OAI_CompactMellinBridge_outsideCoeff_baseChange_zero
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
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge FiniteSFactor
namespace OAI.CompactScaleBridge
theorem _root_.solution
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (D : ℝ)
    (hD : 0 < D) (hSupp : ∀ y : ℝ, 2 ≤ y → W y = 0) :
    HasSum (fun n : ℕ =>
      outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D))
      (realCompactOutsideSum χ S W D) := by
  classical
  let N : ℕ := 2 * Nat.ceil D
  have hNreal : 2 * D ≤ (N : ℝ) := by
    dsimp [N]
    push_cast
    nlinarith [Nat.le_ceil D]
  have hterm (n : ℕ) (hn : n ∉ Finset.Icc 1 N) :
      outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D) = 0 := by
    by_cases hn0 : n = 0
    · subst n
      rw [outsideCoeff_baseChange_zero]
      simp
    · have hn_gt : N < n := by
        simp only [Finset.mem_Icc] at hn
        omega
      have hnreal : (N : ℝ) < n := by exact_mod_cast hn_gt
      have hratio : 2 ≤ (n : ℝ) / D := by
        apply (le_div_iff₀ hD).2
        nlinarith
      simp [hSupp _ hratio]
  have hs : HasSum (fun n : ℕ =>
      outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D))
      (∑ n ∈ Finset.Icc 1 N,
        outsideCoeff S (baseChangeWeight χ) n * W ((n : ℝ) / D)) :=
    hasSum_sum_of_ne_finset_zero hterm
  change HasSum _ (∑ I ∈ outsideIdealsUpTo S N,
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D))
  rw [outsideIdealSum_eq_outsideCoeff_sum S N (baseChangeWeight χ)
    (fun n : ℕ => W ((n : ℝ) / D))]
  exact hs
end OAI.CompactScaleBridge
