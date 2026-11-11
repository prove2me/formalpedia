-- Prove2me | solution 1 for OAI.CubicEisenstein.regularRowKernel_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:55:30.552948+00:00
-- url     : https://prove2.me/submissions/317fa401-3169-4459-9f24-11ed854223cb

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CubicReopening
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_MeromorphicResolvent
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedHeight
import Theorems.Thm_OAI_CubicEisenstein_heightDenominator_eq_quadratic


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
open OAI.CubicEisenstein
open Filter
open scoped BigOperators Classical Topology ContDiff
namespace OAI.CubicEisenstein
theorem _root_.solution (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (u : Fin 2→ℂ)
    (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    regularRowKernel s deltaLoss u p=rowSmoothPower s u p := by
  rw [regularRowKernel,regularSpatialHeight_eq deltaLoss hδ p hp]
  unfold rowSmoothPower spatialHeightPower
  rw [←heightDenominator_eq_quadratic]
  rfl
end OAI.CubicEisenstein
