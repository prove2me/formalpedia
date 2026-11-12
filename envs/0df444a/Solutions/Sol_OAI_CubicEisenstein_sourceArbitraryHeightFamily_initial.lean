-- Prove2me | solution 1 for OAI.CubicEisenstein.sourceArbitraryHeightFamily_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:54:22.724199+00:00
-- url     : https://prove2.me/submissions/407e6c0c-65bd-4195-9c38-f01e50c7d7fb

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
import Theorems.Thm_OAI_CubicEisenstein_sourceProjection_integral
import Theorems.Thm_OAI_CubicEisenstein_arbitraryCuspHeightFamily_initial
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicEisenstein_continuous


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
open CubicKubota
namespace OAI.CubicEisenstein
theorem _root_.solution (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:4<s.re) (hi:0<s.im) :
    sourceArbitraryHeightFamily M a b ha ρ freq s=
      ∫w in cuspPeriodStrip a b,sourceEisenstein s (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [sourceEisenstein,sourceProjection_integral _ (hyperbolicEisenstein_continuous s (by linarith)) M a b ha ρ freq]
  unfold sourceArbitraryHeightFamily
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  exact arbitraryCuspHeightFamily_initial _ a b ha ρ freq s hs hi
end OAI.CubicEisenstein
