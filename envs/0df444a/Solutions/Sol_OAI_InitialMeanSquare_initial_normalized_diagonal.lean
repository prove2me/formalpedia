-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_normalized_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:40:33.62814+00:00
-- url     : https://prove2.me/submissions/4abfcce4-6e3e-4f56-a35b-8324ed0f2bb5

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
import Theorems.Thm_OAI_InitialMeanSquare_initial_diagonal_fixed_profile
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_support


set_option autoImplicit false
open OAI
noncomputable section
open OAI.InitialMeanSquare
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
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)
open EisensteinSchwartzPoisson (paperRadialFourier)
namespace OAI.InitialMeanSquare
theorem _root_.solution
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1)
      (Z Y : ℝ),0<Z → 0<Y →
      ∀K : Finset ι→Finset ι→Finset O,
      (∀G∈F.powerset,∀E∈G.powerset,(0:O)∈K G E) →
      ‖truncatedSecondZero p hg F Ψ 1 1 1
        (fun S => star (normalizedColumn p
          (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) S)) rowMajorant Y K‖≤C*Y := by
  obtain ⟨C,hC,h⟩ := initial_diagonal_fixed_profile (initialLogProfile W a b ha hs hW)
    rowMajorant (|Real.log a|+|Real.log b|+1) (initialLogProfile_support W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ Z Y hZ hY K hK
  exact h p hp hg hinj F Ψ hΨ 1 1 1 Z Y hZ hY K hK
end OAI.InitialMeanSquare
