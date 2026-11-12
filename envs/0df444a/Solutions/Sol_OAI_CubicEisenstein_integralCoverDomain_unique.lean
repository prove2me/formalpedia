-- Prove2me | solution 1 for OAI.CubicEisenstein.integralCoverDomain_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:44:01.783052+00:00
-- url     : https://prove2.me/submissions/6ed90e20-06cf-4f41-a997-5e859169681a

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
import Theorems.Thm_OAI_CubicEisenstein_fundamental_reduction_unique
import Theorems.Thm_OAI_CubicEisenstein_integralCoverRep_mul_projection
import Theorems.Thm_OAI_CubicEisenstein_integralCoverSheet_membership

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
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) (w : HyperbolicSpace)
    (h1 h2 : H) (hh1 : h1•w∈integralCoverDomain H K)
    (hh2 : h2•w∈integralCoverDomain H K) : h1=h2 := by
  obtain ⟨q1,hq1⟩ := Set.mem_iUnion.mp hh1
  obtain ⟨q2,hq2⟩ := Set.mem_iUnion.mp hh2
  have he : integralCoverRep H K q1*Subgroup.inclusion hHK h1=
      integralCoverRep H K q2*Subgroup.inclusion hHK h2 := by
    apply fundamental_reduction_unique K hK _ _ w
    · exact (integralCoverSheet_membership hHK q1 h1 w).mp hq1
    · exact (integralCoverSheet_membership hHK q2 h2 w).mp hq2
  have hqeq : q1=q2 := by
    have hproj := congrArg (fun k : K=>(k : IntegralCoverCosets H K)) he
    rw [integralCoverRep_mul_projection hHK q1 h1,
      integralCoverRep_mul_projection hHK q2 h2] at hproj
    exact hproj
  subst q2
  exact (Subgroup.inclusion_injective hHK) (mul_left_cancel he)
end OAI.CubicEisenstein
