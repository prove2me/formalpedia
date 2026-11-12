-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelCorrespondenceTest_field
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:20:32.458199+00:00
-- url     : https://prove2.me/submissions/c889f29e-80d8-400e-969e-4f14850f614d

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedSixBranches

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
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
namespace OAI.CubicEisenstein
theorem _root_.solution (f : kernelSmoothTests) (p : EuclideanSpatial) :
    kernelTestField (kernelCorrespondenceTest hHK hJK e g he f) p=
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑q : IntegralCoverCosets H globalKubotaKernel,
        kernelTestField f (euclideanAction (kernelCorrespondenceMatrix g q) p) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change kernelCorrespondenceFunction hJK e g he f.1
    (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))=_
  rw [kernelCorrespondenceFunction_lift]
  apply Finset.sum_congr rfl
  intro q _
  change f.1 (integralOrbitProjection globalKubotaKernel
      (kernelCorrespondenceMatrix g q•euclideanToHyperbolic p))=
    f.1 (integralOrbitProjection globalKubotaKernel
      (euclideanToHyperbolic (euclideanAction (kernelCorrespondenceMatrix g q) p)))
  rw [euclideanAction,euclideanToHyperbolic_coordinates]
end OAI.CubicEisenstein
