-- Prove2me | solution 1 for OAI.InitialMeanSquare.mobiusRow_initial_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:14:52.669363+00:00
-- url     : https://prove2.me/submissions/e7a94f37-e35f-44a0-b7c4-c11ba8c43acb

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_normalized
import Theorems.Thm_OAI_InitialMeanSquare_mobiusRow_mul

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
omit [DecidableEq ι]
namespace OAI.InitialMeanSquare
theorem _root_.solution (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z =
      (Real.sqrt Z : ℂ)⁻¹*mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z := by
  have hc : normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) =
      fun T => (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p T/Z) := by
    funext T
    exact initialLogProfile_normalized p hp T Z hZ W a b ha hs hW
  rw [hc, mobiusRow_mul]
end OAI.InitialMeanSquare
