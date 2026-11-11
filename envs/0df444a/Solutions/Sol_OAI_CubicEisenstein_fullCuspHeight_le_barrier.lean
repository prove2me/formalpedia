-- Prove2me | solution 1 for OAI.CubicEisenstein.fullCuspHeight_le_barrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:26:52.287837+00:00
-- url     : https://prove2.me/submissions/64ea824e-7929-4351-bbd7-48eef24fb6d2

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CubicReopening
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_MeromorphicResolvent
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedHeight
import Theorems.Thm_OAI_CubicEisenstein_cuspBarrierProfile_zero
import Theorems.Thm_OAI_CubicEisenstein_cuspTransition_one
import Theorems.Thm_OAI_CubicEisenstein_fullCuspProfileSum_eq_single


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
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups
namespace OAI.CubicEisenstein
theorem _root_.solution (x : FullCuspClasses) (w : HyperbolicSpace) :
    fullCuspHeight x w≤max 3 (cuspBarrier 2 3 w) := by
  by_cases hx : fullCuspHeight x w≤3
  · exact hx.trans (le_max_left _ _)
  · have he : cuspBarrier 2 3 w=fullCuspHeight x w := by
      rw [cuspBarrier,fullCuspProfileSum_eq_single _
        (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) w x (by linarith),
        cuspBarrierProfile,cuspTransition_one 2 3 _ (by norm_num) (by linarith),one_mul]
      ring
    exact he ▸ le_max_right _ _
end OAI.CubicEisenstein
