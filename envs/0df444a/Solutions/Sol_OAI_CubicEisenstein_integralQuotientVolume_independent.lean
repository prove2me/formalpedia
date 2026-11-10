-- Prove2me | solution 1 for OAI.CubicEisenstein.integralQuotientVolume_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:58:46.7991+00:00
-- url     : https://prove2.me/submissions/5a15d09b-35b3-4d81-b5dd-d27e379d0a69

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicFundamentalSet_isFundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_measurable_integralOrbitProjection
import Theorems.Thm_OAI_CubicEisenstein_integralOrbitProjection_eq


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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (H : Subgroup (SL(2,O))) (hH : H≤levelThree)
    (D : Set HyperbolicSpace) (hD : IsFundamentalDomain H D hyperbolicVolume) :
    Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict D)=integralQuotientVolume H := by
  apply Measure.ext
  intro S hS
  have hp := measurable_integralOrbitProjection H
  unfold integralQuotientVolume
  rw [Measure.map_apply hp hS,Measure.map_apply hp hS,Measure.restrict_apply (hp hS),
    Measure.restrict_apply (hp hS)]
  apply hD.measure_set_eq (hyperbolicFundamentalSet_isFundamentalDomain H hH) (hp hS)
  intro M
  ext w
  change integralOrbitProjection H (M • w)∈S ↔ integralOrbitProjection H w∈S
  rw [integralSubgroup_smul,integralOrbitProjection_eq]
end OAI.CubicEisenstein
