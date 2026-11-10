-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalSource_mode_attachment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:49:25.378915+00:00
-- url     : https://prove2.me/submissions/c56b1e5d-983b-4756-978f-600085223198

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialWindows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HarmonicAggregation
import Theorems.Thm_OAI_SecondPassArithmetic_orientedCubeFirstBlock_single_source
import Theorems.Thm_OAI_SecondPassArithmetic_canonical_log_kernel
import Theorems.Thm_OAI_SecondPassArithmetic_commonProductUnit_spec
import Theorems.Thm_OAI_FirstPassCubeLabels_actualFirstKernel_common_unit
import Theorems.Thm_OAI_SecondPassArithmetic_actualFirstKernel_insert_windows


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
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)
variable {ι:Type*} [DecidableEq ι]
  (p:ι→OAI.SecondPassArithmetic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (pool:Finset ι) (b:CubeCoordinates ι) (hb:b.Admissible) (C D:Finset ι)
    (hCB:Disjoint C b.support) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    ((UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ))*
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ (idealGenerator I) (fun U=>g₁ (columnLog p ell U)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ (idealGenerator I) (fun U=>g₂ (columnLog p ell U)))
        W (fun _=>1) (fun _=>1) 1 1 K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h =
    (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*commonCubePhase p hg b C*
      orientedCubeFirstBlock p hp hcop hg pool (sourceGlobalBlock b C D)
        {(I,(commonProductUnit p C:O)^2*h)} (fun _=>1) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  have hFB:Disjoint (pool\(b.support∪C)) b.support :=
    Finset.disjoint_left.mpr (fun i hi hiB=>(Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB))
  rw [canonical_log_kernel p hp hcop hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ (idealGenerator I) _ h g₁ g₂ W K ell hell]
  rw [actualFirstKernel_insert_windows p hp hcop hg _ _ _ _ _ Ψ₁ Ψ₂ m₁ m₂ _ _
    g₁ g₂ W V₁ V₂ _ _ K _ h hV₁ hV₂]
  rw [commonProductUnit_spec p C]
  rw [actualFirstKernel_common_unit p hp hcop hg _ _ hFB _ _ _ _ _ W V₁ V₂ _ _ K
    (commonProductUnit p C) _ (idealGenerator I) _ h]
  rw [orientedCubeFirstBlock_single_source]
  unfold commonCubePhase
  ring
end OAI.SecondPassArithmetic
