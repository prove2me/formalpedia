-- Prove2me | solution 1 for OAI.FirstCauchyArithmetic.idealSexticRow_support_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:25:49.782795+00:00
-- url     : https://prove2.me/submissions/0cd8cba2-ed0c-4995-a5d8-bf785fa030d1

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Theorems.Thm_OAI_ConcretePrimeRowBridge_mem_idealSupport_iff


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
open scoped BigOperators Classical
open OAI.FirstCauchyArithmetic
open ActualEisensteinCubic ConcretePrimeRowBridge
namespace OAI.FirstCauchyArithmetic
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, lambda ∉ P i)
    (B S : Finset ι) (hS : S ⊆ B) (h : O) :
    idealSexticRow (supportIdealFamily P B) (supportIdealFamily_pos P B)
      (supportIdealFamily_good P hg B) (∏ i ∈ S, P i) h =
      finiteSquarefreeRow P hg S h := by
  let F := supportIdealFamily P B
  have hIF : (∏ i ∈ S, P i) ∈ F :=
    Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr hS, rfl⟩
  let idx (i : ι) (hi : i ∈ S) : primePool F :=
    ⟨P i, mem_primePool_iff.mpr ⟨∏ j ∈ S, P j, hIF,
      (factor_family_product_iff P S (P i)).mpr ⟨i, hi, rfl⟩⟩⟩
  symm
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_bij idx
  · intro i hi
    exact (mem_idealSupport_iff F _ (idx i hi)).mpr
      ((factor_family_product_iff P S (P i)).mpr ⟨i, hi, rfl⟩)
  · intro i hi j hj hij
    exact hinj (congrArg Subtype.val hij)
  · intro Q hQ
    have hm := (mem_idealSupport_iff F _ Q).mp hQ
    obtain ⟨i, hi, he⟩ := (factor_family_product_iff P S Q.val).mp hm
    exact ⟨i, hi, Subtype.ext he.symm⟩
  · intro i hi
    rfl
end OAI.FirstCauchyArithmetic
