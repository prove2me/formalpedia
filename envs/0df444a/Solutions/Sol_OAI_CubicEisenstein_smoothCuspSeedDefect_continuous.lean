-- Prove2me | solution 1 for OAI.CubicEisenstein.smoothCuspSeedDefect_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:54:09.869876+00:00
-- url     : https://prove2.me/submissions/c9fc2c6f-26ac-4942-bb07-e8b6613cb292

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialCoordinates_continuous
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialCoordinates_reconstruct
import Theorems.Thm_OAI_CubicEisenstein_smoothCuspSeedDefect_contDiffAt
import Theorems.Thm_OAI_CubicEisenstein_smoothCuspSeedDefect_coordinate


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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    Continuous (smoothCuspSeedDefect a b s) := by
  have heq : smoothCuspSeedDefect a b s=
      fun w => heightPoincareField (cuspSeedDefectProfile a b s) (hyperbolicSpatialCoordinates w) := by
    funext w
    nth_rw 1 [←hyperbolicSpatialCoordinates_reconstruct w]
    exact smoothCuspSeedDefect_coordinate a b s ha hab _ (hyperbolicSpatialCoordinates_positive w)
  rw [heq,continuous_iff_continuousAt]
  intro w
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab _
    (hyperbolicSpatialCoordinates_positive w)).continuousAt.comp
      hyperbolicSpatialCoordinates_continuous.continuousAt
end OAI.CubicEisenstein
