-- Prove2me | solution 1 for OAI.CubicEisenstein.cusp_vertical_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:50:17.028683+00:00
-- url     : https://prove2.me/submissions/fb4fb5a3-eea6-4601-b286-44b04bf4862b

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal
namespace OAI.CubicEisenstein
theorem _root_.solution (F : CuspChartCoordinates → ℂ) (a : ℝ) :
    (∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a)≤
      cuspDirichletEnergy F a := by
  apply lintegral_mono
  intro q
  change ENNReal.ofReal (‖cuspCoordinateVelocity F q 2‖^2)≤_
  exact Finset.single_le_sum (fun j hj => (zero_le : (0:ℝ≥0∞)≤ENNReal.ofReal (‖cuspCoordinateVelocity F q j‖^2))) (Finset.mem_univ (2:Fin 3))
end OAI.CubicEisenstein
