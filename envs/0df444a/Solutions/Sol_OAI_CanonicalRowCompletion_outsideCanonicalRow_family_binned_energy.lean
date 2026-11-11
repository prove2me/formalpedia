-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.outsideCanonicalRow_family_binned_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:43:07.966534+00:00
-- url     : https://prove2.me/submissions/7c0d888f-ddf9-41a5-8ef6-5f31da2f6cba

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoordinateLaplacian
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DensityBudgets
import Theorems.Thm_OAI_CanonicalRowCompletion_rowFamilyEnergy_bound_sum
import Theorems.Thm_OAI_CanonicalRowCompletion_outsideCanonicalRow_binned_energy


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
open MeasureTheory
open scoped BigOperators Classical
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.CanonicalRowCompletion
theorem _root_.solution
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ K : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hK : 0 < K)
    (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    rowFamilyEnergy labels (fun I z => outsideCanonicalRow S D hbad Ψ m (idealGenerator I) z W X) K ≤
      2*X*(rowFamilyEnergy labels (fun I z =>
        shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          rowFamilyEnergy labels (fun I z =>
            outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀) K) := by
  apply rowFamilyEnergy_bound_sum labels (cubeLogRange b X) K hK
  intro I hI z hz
  exact outsideCanonicalRow_binned_energy S D hbad hSp Ψ m (idealGenerator I) z W hWc
    b X H₀ hb hX hW hD
end OAI.CanonicalRowCompletion
