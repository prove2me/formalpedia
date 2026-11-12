-- Prove2me | solution 1 for OAI.CubicEisenstein.ramifiedScaledMode_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:03:34.747661+00:00
-- url     : https://prove2.me/submissions/d3f223fc-262c-47dc-a86e-8d449c9c9793

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedSixBranches
import Theorems.Thm_OAI_CubicEisenstein_ramifiedSource_weighted_shift

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
open scoped BigOperators Classical Topology MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (b : Bool) (h x : Eis) (v : ℝ) (hv : 0<v) (z : ℂ) :
    ramifiedScaledMode b h v hv (z+eisEmbedding x)=
      affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*ramifiedScaledMode b h v hv z := by
  unfold ramifiedScaledMode
  rw [show 3*(z+eisEmbedding x)=3*z+3*eisEmbedding x by ring]
  have h1 : -cuspFrequency h*(z+eisEmbedding x)=
      -ninthCuspFrequency h*(3*z+3*eisEmbedding x) := by rw [ninthCuspFrequency];ring
  have h2 : -cuspFrequency h*z= -ninthCuspFrequency h*(3*z) := by rw [ninthCuspFrequency];ring
  rw [h1,h2]
  exact ramifiedSource_weighted_shift b h x (3*z) v hv
end OAI.CubicEisenstein
