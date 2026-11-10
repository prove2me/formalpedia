-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelLocalLift_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:55:03.593517+00:00
-- url     : https://prove2.me/submissions/754c9bf1-84f9-44d5-bdcc-885e40a23077

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotient_localHomeomorph


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
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (w : HyperbolicSpace) :
    (kernelLocalLift w).symm=integralOrbitProjection globalKubotaKernel :=
  kernelQuotient_localHomeomorph.localInverseAt_symm w
end OAI.CubicEisenstein
