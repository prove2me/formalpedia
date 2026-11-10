-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelQuotientBarrier_fordCusp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:15:11.027941+00:00
-- url     : https://prove2.me/submissions/a0f71777-9944-4a7e-8d67-03bb7563a58d

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Theorems.Thm_OAI_CubicEisenstein_cuspBarrier_high

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
open scoped BigOperators Classical Topology ContDiff MatrixGroups
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (M : SL(2,ActualEisensteinCubic.O)) (p : UpperCoordinates) (hp : b<p.1.2) :
    kernelQuotientBarrier a b (fordOrbitChart globalKubotaKernel M p)=p.1.2 :=
  cuspBarrier_high a b ha hab M⁻¹ p.1.1 p.1.2 p.2 hp
end OAI.CubicEisenstein
