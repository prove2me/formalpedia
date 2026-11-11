-- Prove2me | solution 1 for OAI.CubicKubota.finite_rational_representatives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:16:36.834195+00:00
-- url     : https://prove2.me/submissions/5561c6b9-98a1-4183-b8a1-69d7dd51cb77

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
open CubicEisenstein
namespace OAI.CubicKubota
theorem _root_.solution : ∃R : Finset (SL(2,ℤ)),
    ∀g : levelTwo,∃r∈R,(g:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding r)⁻¹∈levelThree := by
  let : Fintype (levelTwo ⧸ levelThreeInTwo) := Fintype.ofFinite _
  let sectionMap : (levelTwo ⧸ levelThreeInTwo)→SL(2,ℤ) :=
    fun q => (rationalQuotient_surjective q).choose
  have hsection : ∀q,rationalQuotient (sectionMap q)=q :=
    fun q => (rationalQuotient_surjective q).choose_spec
  refine ⟨Finset.univ.image sectionMap,fun g => ?_⟩
  let q := QuotientGroup.mk' levelThreeInTwo g
  refine ⟨sectionMap q,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩
  have he : QuotientGroup.mk' levelThreeInTwo (g*(rationalLift (sectionMap q))⁻¹)=1 := by
    rw [map_mul,map_inv]
    change q*(rationalQuotient (sectionMap q))⁻¹=1
    rw [hsection,mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff (N:=levelThreeInTwo)
    (g*(rationalLift (sectionMap q))⁻¹)).mp he
end OAI.CubicKubota
