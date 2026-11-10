-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstTruncatedSource_eq_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:27:53.058059+00:00
-- url     : https://prove2.me/submissions/84a88f41-a0b5-4bd0-a5eb-be34c9997c00

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondLiteralTerm_zero_of_not_support
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstTruncatedSource_eq_literal
import Theorems.Thm_OAI_SecondPassArithmetic_mem_globalFirstExpansionPool
import Theorems.Thm_OAI_SecondPassArithmetic_mem_secondExpansionPool


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
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell M : ℝ) (hell : 0<ell)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      ∑ ray : SecondRayIndex,∑ x∈globalFirstSupportedPool p pool s cutoff ell M side,
        w x.first*globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell (Y x.first) side x := by
  rw [globalFirstTruncatedSource_eq_literal p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro ray hray
  unfold globalFirstSupportedPool
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source
  · rw [if_pos hs]
  · rw [if_neg hs,globalSecondLiteralTerm_zero_of_not_support p hp hcop hg hinj pool Ψ m ray g W ell (Y x.first) M side x hell hgM]
    · ring
    · exact ((mem_secondExpansionPool _ _ _).mp ((mem_globalFirstExpansionPool pool s cutoff x).mp hx).2).2.1
    · exact hs
end OAI.SecondPassArithmetic
