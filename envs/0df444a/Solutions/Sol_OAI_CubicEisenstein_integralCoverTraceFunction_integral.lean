-- Prove2me | solution 1 for OAI.CubicEisenstein.integralCoverTraceFunction_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:03:30.475198+00:00
-- url     : https://prove2.me/submissions/67fa903a-d186-43d6-a9f4-727e24ef94a8

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
import Theorems.Thm_OAI_CubicEisenstein_integralCoverDomain_projection_measurePreserving
import Theorems.Thm_OAI_CubicEisenstein_integralCoverFiber_integrable
import Theorems.Thm_OAI_CubicEisenstein_integralCoverFiber_integral
import Theorems.Thm_OAI_CubicEisenstein_integralCoverSheet_measurable
import Theorems.Thm_OAI_CubicEisenstein_integralCoverSheet_pairwiseDisjoint
import Theorems.Thm_OAI_CubicEisenstein_integralCoverTraceFunction_measurable
import Theorems.Thm_OAI_CubicEisenstein_integralQuotientVolume_integral
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
open OAI.CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : Integrable f (integralQuotientVolume H)) :
    (∫q,integralCoverTraceFunction H K f q∂integralQuotientVolume K)=
      ∫q,f q∂integralQuotientVolume H := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hD := (integralCoverDomain_projection_measurePreserving hHK hK).integrable_comp_of_integrable hf
  have hS (q : IntegralCoverCosets H K) : IntegrableOn (fun w=>f (integralOrbitProjection H w))
      (integralCoverSheet H K q) hyperbolicVolume :=
    IntegrableOn.mono_set hD (Set.subset_iUnion (integralCoverSheet H K) q)
  rw [integralQuotientVolume_integral K _
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable]
  change (∫w in hyperbolicFundamentalSet K,
    ∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)∂hyperbolicVolume)=_
  rw [integral_finsetSum Finset.univ (fun q _=>integralCoverFiber_integrable hHK hK f hmeas hf q)]
  simp_rw [integralCoverFiber_integral H K]
  rw [←integral_iUnion_fintype (integralCoverSheet_measurable H K)
    (integralCoverSheet_pairwiseDisjoint H K hK) hS]
  change (∫w in integralCoverDomain H K,f (integralOrbitProjection H w)∂hyperbolicVolume)=_
  rw [←(integralCoverDomain_projection_measurePreserving hHK hK).map_eq]
  exact (integral_map (measurable_integralOrbitProjection H).aemeasurable hmeas.aestronglyMeasurable).symm
end OAI.CubicEisenstein
