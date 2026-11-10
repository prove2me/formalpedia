-- Prove2me | solution 1 for OAI.InitialMeanSquare.selectedIdealTest_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:14:55.204462+00:00
-- url     : https://prove2.me/submissions/ece5208a-2606-4c56-afd6-280c06be2508

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_OutsideIdeals
import Theorems.Thm_OAI_InitialMeanSquare_outside_pool_product_not_dvd
import Theorems.Thm_OAI_InitialMeanSquare_poolPrimary_norm
import Theorems.Thm_OAI_InitialMeanSquare_poolProduct_admissible


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
theorem _root_.solution (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hs : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D)
    (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    selectedIdealTest (outsideSquarefreeIdeals S D) (fun n => W (n/Z)) T =
    W (primeProductNorm (poolPrimary (outsideSquarefreeIdeals S D)) T/Z) := by
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  rw [poolPrimary_norm F hF T]
  unfold selectedIdealTest
  by_cases hw : W ((Ideal.absNorm (∏ i ∈ T,i.val) : ℝ)/Z)=0
  · split_ifs
    · rfl
    · exact hw.symm
  · rw [if_pos]
    have ha := poolProduct_admissible F hF T
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,outside_pool_product_not_dvd S D hSp T⟩,ha.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (fun hz => ha.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact_mod_cast ((div_le_iff₀ hZ).mp (hs _ hw)).trans hD
end OAI.InitialMeanSquare
