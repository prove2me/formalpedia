-- Prove2me | solution 1 for OAI.CubicEisenstein.coverEnergyDensity_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:42:02.093556+00:00
-- url     : https://prove2.me/submissions/0222b720-2ada-4fc3-8407-d81daa844287

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
import Theorems.Thm_OAI_CubicEisenstein_coverGradientAt_norm_sq
import Theorems.Thm_OAI_CubicEisenstein_coverGradientAt_sum
import Theorems.Thm_OAI_CubicEisenstein_norm_sum_sq_le_card

set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
namespace OAI.CubicEisenstein
theorem _root_.solution {ι : Type*} (s : Finset ι) (F : ι→EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hF : ∀i∈s,DifferentiableAt ℝ (F i) p) :
    coverEnergyDensity (fun x=>∑i∈s,F i x) p≤(s.card:ℝ)*∑i∈s,coverEnergyDensity (F i) p := by
  rw [←coverGradientAt_norm_sq _ _ (DifferentiableAt.fun_sum hF),coverGradientAt_sum s F p hF]
  have hh := norm_sum_sq_le_card s (fun i=>coverGradientAt (F i) p)
  calc
    _ ≤ _ := hh
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact coverGradientAt_norm_sq (F i) p (hF i hi)
end OAI.CubicEisenstein
