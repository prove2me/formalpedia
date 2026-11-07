-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.mobius_column_after_dual_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:40.190752+00:00
-- url     : https://prove2.me/submissions/15bcf296-8912-4ab4-a266-0d12769f2bd9

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Theorems.Thm_OAI_FirstPassCubeLabels_first_pass_after_dual_dilation

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
open scoped BigOperators Classical
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
namespace OAI.FirstPassCubeLabels
theorem _root_.solution
    {ι κ : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (columns : Finset ι) (C : Finset ι → ℂ)
    (p : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (z : O) :
    (∑ S ∈ columns.powerset, FirstCauchyArithmetic.supportMobius P S * C S *
      ((rowCoprimeMask P S (cubeRadical p B) *
        finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
        star (finiteSquarefreeRow P hg S z))) =
    FirstCauchyArithmetic.supportConjugateSum P hg columns
      (fun S => C S * finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
        rowCoprimeMask P S (b0Label p B v ε₁ ε₂))
      (z * dilationLabel p B v ε₁ ε₂) := by
  unfold FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_congr rfl
  intro S hS
  rw [first_pass_after_dual_dilation P hg S p B v ε₁ ε₂ hv side z]
  ring
end OAI.FirstPassCubeLabels
