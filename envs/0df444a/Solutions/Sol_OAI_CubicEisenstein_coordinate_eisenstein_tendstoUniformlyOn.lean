-- Prove2me | solution 1 for OAI.CubicEisenstein.coordinate_eisenstein_tendstoUniformlyOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:05:35.680197+00:00
-- url     : https://prove2.me/submissions/de6df466-d21e-4256-aba6-541558c4d2cd

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_TruncatedSecondTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_TwistedProfiles
import Theorems.Thm_OAI_CubicEisenstein_coordinate_summable_majorant

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
open OAI.CubicEisenstein
open Filter
open scoped BigOperators Classical MatrixGroups Matrix Topology
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
namespace OAI.CubicEisenstein
theorem _root_.solution (C a b : ℝ) (hC : 0<C)
    (ha : 2<a) (hb : 2<b) :
    TendstoUniformlyOn
      (fun f : Finset CuspCosets => fun p : UpperCoordinates × ℂ =>
        ∑ x ∈ f, summand (coordinateSection p.1) p.2 x)
      (fun p => eisenstein (coordinateSection p.1) p.2) atTop
      {p | rowBound (coordinateSection p.1) ≤ C ∧ a ≤ p.2.re ∧ p.2.re ≤ b} := by
  obtain ⟨M,hM,_,hbound⟩ := coordinate_summable_majorant C a b hC ha hb
  exact tendstoUniformlyOn_tsum hM (fun x p hp => hbound p hp.1 hp.2.1 hp.2.2 x)
end OAI.CubicEisenstein
