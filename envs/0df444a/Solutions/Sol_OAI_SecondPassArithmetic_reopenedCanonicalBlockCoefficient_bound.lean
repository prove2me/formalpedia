-- Prove2me | solution 1 for OAI.SecondPassArithmetic.reopenedCanonicalBlockCoefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:05:28.108046+00:00
-- url     : https://prove2.me/submissions/f0095633-57cd-47f8-8014-0f3867e1f2b9

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalTailBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopenedFibers
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedPairCoefficient_bound
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalBlockCoefficient_bound


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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
namespace OAI.SecondPassArithmetic
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hβ : ∀ I ∈ labels,∀ v ∈ Q,‖β I v‖ ≤ Γ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀ u,‖Ψ u‖ ≤ 1) (m : ActualEisensteinCubic.O) (K ell : ℝ)
    (b : GlobalCubeBlock ι) (hb : b ∈ canonicalSourceBlocks pool (reopenedCubeFamily Q))
    (x : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) (hx : x ∈ canonicalBlockFrequencies p K ell labels b) :
    ‖canonicalBlockCoefficient p hp hcop hg (reopenedPairCoefficient β) Ψ Ψ m m b x‖ ≤ Γ^2 := by
  exact canonicalBlockCoefficient_bound p hp hcop hg hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m (Γ^2) K ell (sq_nonneg _) hΨ hΨ
    (fun b hb C hC I hI => reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb C I hI) b hb x hx
end OAI.SecondPassArithmetic
