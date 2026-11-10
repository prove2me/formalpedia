-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelProjection_measure_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:23:19.912991+00:00
-- url     : https://prove2.me/submissions/760c2eea-fffe-4c0d-892a-543f56168435

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Theorems.Thm_OAI_CubicEisenstein_integralOrbitProjection_preimage_image
import Theorems.Thm_OAI_CubicEisenstein_kernelProjection_translates_disjoint
import Theorems.Thm_OAI_CubicEisenstein_continuous_integralOrbitProjection
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_isFundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicFundamentalSet_measurable
import Theorems.Thm_OAI_CubicEisenstein_measurable_integralOrbitProjection


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
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
namespace OAI.CubicEisenstein
theorem _root_.solution (S : Set HyperbolicSpace) (hS : MeasurableSet S)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    integralQuotientVolume globalKubotaKernel (integralOrbitProjection globalKubotaKernel '' S)=
      hyperbolicVolume S := by
  have himg := hS.image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn hinj
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection _) himg,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) himg),
    integralOrbitProjection_preimage_image,Set.iUnion_inter]
  rw [measure_iUnion]
  · exact (globalKubotaKernel_isFundamentalDomain.measure_eq_tsum S).symm
  · intro M N hMN
    exact (kernelProjection_translates_disjoint S hinj hMN).mono Set.inter_subset_left Set.inter_subset_left
  · intro M
    exact (hS.const_smul M).inter (hyperbolicFundamentalSet_measurable _)
end OAI.CubicEisenstein
