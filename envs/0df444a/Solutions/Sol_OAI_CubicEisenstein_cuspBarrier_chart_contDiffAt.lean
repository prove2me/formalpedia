-- Prove2me | solution 1 for OAI.CubicEisenstein.cuspBarrier_chart_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:14:57.935234+00:00
-- url     : https://prove2.me/submissions/1db26ded-80ad-484b-9c22-92f21e169bb9

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Theorems.Thm_OAI_CubicEisenstein_cuspBarrierProfile_smooth
import Theorems.Thm_OAI_CubicEisenstein_cuspBarrierProfile_zero
import Theorems.Thm_OAI_CubicEisenstein_fullCuspProfileSum_chart_contDiffAt

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
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => cuspBarrier a b (hyperbolicSpatialChart.symm q)) p :=
  contDiffAt_const.add (fullCuspProfileSum_chart_contDiffAt _
    (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha))
    (cuspBarrierProfile_smooth a b) p hp)
end OAI.CubicEisenstein
