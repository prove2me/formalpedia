-- Prove2me | solution 1 for OAI.CubicKubota.twentyFour_rational_representatives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:17:50.966204+00:00
-- url     : https://prove2.me/submissions/0681965d-0b40-449c-aead-3a7b8459ce8b

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedGaussSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_KubotaCharacter
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceProjection

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
open scoped BigOperators Classical
open OAI.CubicKubota
open scoped Classical MatrixGroups
open ActualEisensteinCubic
namespace OAI.CubicKubota
theorem _root_.solution (g : levelTwo) :
    ∃i : RationalBruhatIndex,
      (g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding (rationalBruhatRep i))⁻¹∈levelThree := by
  obtain ⟨r,hr⟩ := rationalQuotient_surjective (QuotientGroup.mk' levelThreeInTwo g)
  obtain ⟨i,hi⟩ := rationalBruhat_complete (rationalReductionThree r)
  refine ⟨i,?_⟩
  have hred : rationalReductionThree (r*(rationalBruhatRep i)⁻¹)=1 := by
    rw [map_mul,map_inv,hi,mul_inv_cancel]
  have hker := (rationalReductionThree_eq_one_iff _).mp hred
  have hquot : rationalQuotient r=rationalQuotient (rationalBruhatRep i) := by
    have hz : rationalQuotient (r*(rationalBruhatRep i)⁻¹)=1 := hker
    rw [map_mul,map_inv,mul_inv_eq_one] at hz
    exact hz
  have he : QuotientGroup.mk' levelThreeInTwo
      (g*(rationalLift (rationalBruhatRep i))⁻¹)=1 := by
    rw [map_mul,map_inv,←hr,hquot]
    exact mul_inv_cancel _
  exact (QuotientGroup.eq_one_iff (N:=levelThreeInTwo)
    (g*(rationalLift (rationalBruhatRep i))⁻¹)).mp he
end OAI.CubicKubota
