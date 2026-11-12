-- Prove2me | solution 1 for OAI.CubicEisenstein.eisensteinTorusMul_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:36:50.619486+00:00
-- url     : https://prove2.me/submissions/0d9dceaa-0d9b-4a56-b9cb-bd2daafdf0d1

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeResidueStrata
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedCuspPhases
import Theorems.Thm_OAI_CubicEisenstein_eisensteinTorusMul_continuous
import Theorems.Thm_OAI_CubicEisenstein_eisensteinTorusMul_surjective

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
open scoped BigOperators Classical Topology
open ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
attribute [local instance] OAI.CubicEisenstein._p2m_local_instance_8a0d29538b_510
attribute [local instance] OAI.CubicEisenstein._p2m_local_instance_8a0d29538b_511
attribute [local instance] OAI.CubicEisenstein._p2m_local_instance_8a0d29538b_513
namespace OAI.CubicEisenstein
theorem _root_.solution (b : ActualEisensteinCubic.O) (hb : b≠0) :
    MeasurePreserving (eisensteinTorusMul b) volume volume :=
  AddMonoidHom.measurePreserving (eisensteinTorusMul_continuous b) (eisensteinTorusMul_surjective b hb) rfl
end OAI.CubicEisenstein
