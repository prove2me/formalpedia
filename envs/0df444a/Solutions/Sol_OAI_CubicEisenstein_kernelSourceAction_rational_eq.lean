-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelSourceAction_rational_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:49:07.660159+00:00
-- url     : https://prove2.me/submissions/eea86509-4ca6-45b0-a4f7-fd309edaba4e

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceProjection
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceQuotient
import Theorems.Thm_OAI_CubicEisenstein_kernelSourceAction_of_kernel
import Theorems.Thm_OAI_CubicEisenstein_rationalCongruenceThree_in_kernel

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open OAI.CubicEisenstein
open CubicKubota
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (r s : SL(2,ℤ))
    (hrs : rationalReductionThree r=rationalReductionThree s) (q : SourceKernelQuotient) :
    kernelSourceAction (rationalLift r) q=kernelSourceAction (rationalLift s) q := by
  have hd : r*s⁻¹∈rationalCongruenceThree := by
    apply (rationalReductionThree_eq_one_iff _).mp
    rw [map_mul,map_inv,hrs,mul_inv_cancel]
  have hk := rationalCongruenceThree_in_kernel _ hd
  have he : rationalLift r=rationalLift (r*s⁻¹)*rationalLift s := by
    rw [←map_mul,inv_mul_cancel_right]
  rw [he,kernelSourceAction_mul]
  exact kernelSourceAction_of_kernel _ hk _
end OAI.CubicEisenstein
