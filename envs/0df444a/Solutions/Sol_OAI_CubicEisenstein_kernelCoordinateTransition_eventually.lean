-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelCoordinateTransition_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:13:34.938225+00:00
-- url     : https://prove2.me/submissions/b556ff75-97c3-45dd-90e4-f2b1ba336de7

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_project
import Theorems.Thm_OAI_CubicEisenstein_kernel_lifts_eventually_deck
import Theorems.Thm_OAI_CubicEisenstein_mobiusSpatial_coordinates_global
import Theorems.Thm_OAI_CubicEisenstein_continuous_integralOrbitProjection


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
theorem _root_.solution (w : HyperbolicSpace) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target)
    (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift w).source) :
    ∃M : globalKubotaKernel,kernelCoordinateTransition w=ᶠ[𝓝 p]
      mobiusSpatial (integralComplexMatrix M) := by
  have hc : ContinuousAt hyperbolicSpatialChart.symm p :=
    hyperbolicSpatialChart.symm.continuousAt hp
  have hπ : ContinuousAt (fun y => integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)) p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp hc
  have hl : ContinuousAt (fun y => kernelLocalLift w (integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y))) p :=
    ((kernelLocalLift w).continuousAt hq).comp
      (f := fun y : SpatialCoordinates => integralOrbitProjection globalKubotaKernel
        (hyperbolicSpatialChart.symm y)) hπ
  have hqn : ∀ᶠ y in 𝓝 p,integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)∈(kernelLocalLift w).source :=
    hπ ((kernelLocalLift w).open_source.mem_nhds hq)
  have hproj : (fun y => integralOrbitProjection globalKubotaKernel (kernelLocalLift w
      (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y))))=ᶠ[𝓝 p]
      (fun y => integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y)) := by
    filter_upwards [hqn] with y hy
    exact kernelLocalLift_project hy
  obtain ⟨M,hM⟩ := kernel_lifts_eventually_deck hl hc hproj
  refine ⟨M,?_⟩
  filter_upwards [hM,hyperbolicSpatialChart.open_target.mem_nhds hp] with y hy hyt
  change hyperbolicSpatialCoordinates _=mobiusSpatial _ y
  rw [hy,mobiusSpatial_coordinates_global]
  exact congrArg _ (hyperbolicSpatialChart.right_inv hyt)
end OAI.CubicEisenstein
