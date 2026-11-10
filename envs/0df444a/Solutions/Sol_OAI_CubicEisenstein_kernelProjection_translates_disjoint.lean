-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelProjection_translates_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:18:51.488389+00:00
-- url     : https://prove2.me/submissions/adc4e4e1-f8e3-429f-ba13-ddf7128fe403

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_le_levelThree
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
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
namespace OAI.CubicEisenstein
theorem _root_.solution (S : Set HyperbolicSpace)
    (hS : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    Pairwise (fun M N : globalKubotaKernel => Disjoint (M • S) (N • S)) := by
  let : IsCancelSMul globalKubotaKernel HyperbolicSpace :=
    integralSubgroupFree globalKubotaKernel globalKubotaKernel_le_levelThree
  intro M N hMN
  apply Set.disjoint_left.mpr
  rintro _ ⟨w,hw,rfl⟩ ⟨u,hu,he⟩
  have hwu : w=u := hS hw hu (by
    calc
      integralOrbitProjection globalKubotaKernel w=
          integralOrbitProjection globalKubotaKernel (M • w) := (integralOrbitProjection_eq _ M w).symm
      _=integralOrbitProjection globalKubotaKernel (N • u) := congrArg _ he.symm
      _=integralOrbitProjection globalKubotaKernel u := integralOrbitProjection_eq _ N u)
  subst u
  exact hMN (IsCancelSMul.right_cancel M N w he.symm)
end OAI.CubicEisenstein
