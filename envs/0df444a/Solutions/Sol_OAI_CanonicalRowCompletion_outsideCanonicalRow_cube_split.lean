-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.outsideCanonicalRow_cube_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:51:54.887197+00:00
-- url     : https://prove2.me/submissions/098043ea-4649-4f6a-8770-8d5f36f9fb4f

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactEnergyFamilies
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_SupportBounds
import Theorems.Thm_OAI_CanonicalRowCompletion_outsideCanonicalRow_eq_global
import Theorems.Thm_OAI_CompletedGauss_completed_cube_inverse_split


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
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
namespace OAI.CanonicalRowCompletion
theorem _root_.solution (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B *
        summand (rowTwist Ψ (m*excludedGenerator S) f z) W X I B := by
  rw [outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b X hX hW hD]
  exact completed_cube_inverse_split _ W hWc X H₀ hX
end OAI.CanonicalRowCompletion
