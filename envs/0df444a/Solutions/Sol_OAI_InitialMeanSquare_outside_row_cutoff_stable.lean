-- Prove2me | solution 1 for OAI.InitialMeanSquare.outside_row_cutoff_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:49:47.93759+00:00
-- url     : https://prove2.me/submissions/accfae14-2bfa-42be-bc11-3d86d8f68b5c

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DualZeroMode
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
import Theorems.Thm_OAI_InitialMeanSquare_outsideIdealsUpTo_mono
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealSexticRow_ambient


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
namespace OAI.InitialMeanSquare
theorem _root_.solution (S : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ S)
    {D E : ℕ} (hDE : D ≤ E) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D) (z : O) :
    idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z =
    idealRowSum (outsideIdealsUpTo S E) (outsideIdealsUpTo_ne_bot S E)
      (outside_good S E hbad) χ (fun n => W (n/Z)) z := by
  have hsub := outsideIdealsUpTo_mono S hDE
  unfold idealRowSum
  calc
    _ = ∑ I ∈ outsideIdealsUpTo S D,
        ShortDraftHeckeBridge.baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ)/Z) *
        idealSexticRow (outsideIdealsUpTo S E) (outsideIdealsUpTo_ne_bot S E)
          (outside_good S E hbad) I z := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [idealSexticRow_ambient (outsideIdealsUpTo S D) (outsideIdealsUpTo S E)
        (outsideIdealsUpTo_ne_bot S D) (outsideIdealsUpTo_ne_bot S E)
        (outside_good S D hbad) (outside_good S E hbad) I hI (hsub hI) z]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro I hIE hID
      have hw : W ((Ideal.absNorm I : ℝ)/Z) = 0 := by
        by_contra hn
        have hbound : (Ideal.absNorm I : ℝ) ≤ D :=
          ((div_le_iff₀ hZ).mp (hW _ hn)).trans hD
        have hnat : Ideal.absNorm I ≤ D := by exact_mod_cast hbound
        obtain ⟨hpos,_,hS⟩ := mem_outsideIdealsUpTo.mp hIE
        exact hID (mem_outsideIdealsUpTo.mpr ⟨hpos,hnat,hS⟩)
      rw [hw,mul_zero,zero_mul]
end OAI.InitialMeanSquare
