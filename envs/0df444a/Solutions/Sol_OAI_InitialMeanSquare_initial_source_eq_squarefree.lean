-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_source_eq_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:48:00.243871+00:00
-- url     : https://prove2.me/submissions/d571e783-84fe-4371-8b87-b0786eb631c6

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Theorems.Thm_OAI_InitialMeanSquare_initial_weight_squarefree

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
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open CanonicalQuadraticSieve (Admissible)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
namespace OAI.InitialMeanSquare
theorem _root_.solution (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (F : Finset ι) (s : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s H₁ H₂ W Y =
      secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (initialSquarefreeSector p s) H₁ H₂ W Y := by
  unfold secondExpansionSource initialSquarefreeSector
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : Squarefree (Ideal.span {(sourceObservation p x).2})
  · rw [if_pos hs]
  · rw [if_neg hs]
    have hw : secondArithmeticWeight p hp hcop hg Ψ m 1 1 ray x=0 := by
      by_contra hn
      exact hs (initial_weight_squarefree p hp hcop hg Ψ m ray x (hE x hx) hn)
    unfold secondArithmeticWeight at hw
    rcases mul_eq_zero.mp hw with h1 | h2
    · rw [h1]
      ring
    · rw [h2]
      ring
end OAI.InitialMeanSquare
