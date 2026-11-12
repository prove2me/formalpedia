-- Prove2me | solution 1 for OAI.CubicEisenstein.integralCoverDomain_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:43:50.803938+00:00
-- url     : https://prove2.me/submissions/66977bdf-cb6b-4f0d-841c-a4657aa52e76

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
import Theorems.Thm_OAI_CubicEisenstein_integralCoverSheet_membership
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicFundamentalSet_covers


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
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding
open OAI.CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (w : HyperbolicSpace) :
    ∃h : H,h•w∈integralCoverDomain H K := by
  obtain ⟨k,hk⟩ := hyperbolicFundamentalSet_covers K w
  let q : IntegralCoverCosets H K := k
  let r := integralCoverRep H K q
  have hr : r⁻¹*k∈H.subgroupOf K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  let h : H := ⟨((r⁻¹*k:K):SL(2,ActualEisensteinCubic.O)),hr⟩
  have hin : Subgroup.inclusion hHK h=r⁻¹*k := rfl
  refine ⟨h,Set.mem_iUnion.mpr ⟨q,?_⟩⟩
  apply (integralCoverSheet_membership hHK q h w).mpr
  change (r*Subgroup.inclusion hHK h)•w∈hyperbolicFundamentalSet K
  rw [hin,mul_inv_cancel_left]
  exact hk
end OAI.CubicEisenstein
