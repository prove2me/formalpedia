-- Prove2me | solution 1 for OAI.CubicEisenstein.integralCoverTraceFunction_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:57:45.871229+00:00
-- url     : https://prove2.me/submissions/d16f5254-a9b4-416d-9ca2-bd85c4b0ddb9

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
import Theorems.Thm_OAI_CubicEisenstein_integralCoverFiber_integrable
import Theorems.Thm_OAI_CubicEisenstein_integralCoverTraceFunction_measurable
import Theorems.Thm_OAI_CubicEisenstein_quotient_projection_measurePreserving


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
    Integrable (integralCoverTraceFunction H K f) (integralQuotientVolume K) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply ((quotient_projection_measurePreserving K).integrable_comp
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable).mp
  change Integrable (fun w=>∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)) _
  exact integrable_finsetSum Finset.univ (fun q _=>integralCoverFiber_integrable hHK hK f hmeas hf q)
end OAI.CubicEisenstein
