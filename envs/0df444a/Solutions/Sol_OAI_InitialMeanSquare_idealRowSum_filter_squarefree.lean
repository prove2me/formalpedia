-- Prove2me | solution 1 for OAI.InitialMeanSquare.idealRowSum_filter_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:05:02.897195+00:00
-- url     : https://prove2.me/submissions/c53ce461-0634-4b77-878f-2cc1c5441234

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_OutsideIdeals
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealSexticRow_ambient
import Theorems.Thm_OAI_ConcretePrimeRowBridge_baseChangeWeight_zero_of_not_squarefree
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
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
namespace OAI.InitialMeanSquare
theorem _root_.solution (F : Finset (Ideal O))
    (hFp : ∀ I ∈ F, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      goodLambda ∉ P) {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (z : O) :
    idealRowSum F hFp hFg χ W z =
    idealRowSum (F.filter Squarefree)
      (fun I hI => hFp I (Finset.mem_filter.mp hI).1)
      (fun I hI => hFg I (Finset.mem_filter.mp hI).1) χ W z := by
  unfold idealRowSum
  calc
    _ = ∑ I ∈ F.filter Squarefree,
        ShortDraftHeckeBridge.baseChangeWeight χ I * W (Ideal.absNorm I) *
          idealSexticRow F hFp hFg I z := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro I hIF hIn
      have hs : ¬ Squarefree I := fun h => hIn (Finset.mem_filter.mpr ⟨hIF,h⟩)
      rw [baseChangeWeight_zero_of_not_squarefree χ I hs, zero_mul, zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [idealSexticRow_ambient F (F.filter Squarefree) hFp
        (fun J hJ => hFp J (Finset.mem_filter.mp hJ).1) hFg
        (fun J hJ => hFg J (Finset.mem_filter.mp hJ).1) I
        (Finset.mem_filter.mp hI).1 hI z]
end OAI.InitialMeanSquare
