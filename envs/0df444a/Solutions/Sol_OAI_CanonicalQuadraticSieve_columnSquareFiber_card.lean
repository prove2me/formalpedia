-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.columnSquareFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:54:30.344202+00:00
-- url     : https://prove2.me/submissions/b2a0e39b-0b0e-42df-8abc-9e354c1f7174

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnSquareFiber_injective
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnSquareFiber_bounds
import Theorems.Thm_OAI_DescentFiberCost_finite_ideal_count_real


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
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hscale : 1≤X/(Ideal.absNorm A:ℝ)^2) :
    ((columnSquareFiber S A).card:ℝ)≤128*(X/(Ideal.absNorm A:ℝ)^2) := by
  let T := (columnSquareFiber S A).image squarefreePart
  have hcard : T.card=(columnSquareFiber S A).card := Finset.card_image_iff.mpr (by
    intro I hI J hJ he
    have hh : (⟨I,hI⟩:columnSquareFiber S A)=(⟨J,hJ⟩:columnSquareFiber S A) :=
      columnSquareFiber_injective S A he
    exact congrArg Subtype.val hh)
  rw [←hcard]
  apply DescentFiberCost.finite_ideal_count_real T _ hscale
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).1.1
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).2
end OAI.CanonicalQuadraticSieve
