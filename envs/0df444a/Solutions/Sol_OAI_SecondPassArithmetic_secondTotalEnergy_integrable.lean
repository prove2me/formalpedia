-- Prove2me | solution 1 for OAI.SecondPassArithmetic.secondTotalEnergy_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:23.725922+00:00
-- url     : https://prove2.me/submissions/49923b0f-bd99-4af4-af1a-10e73a126243

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayCoefficients
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SecondPoisson
import Theorems.Thm_OAI_SecondPassArithmetic_secondTotalEnergy_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_secondTotalEnergy_continuous
import Theorems.Thm_OAI_SecondPassArithmetic_secondTotalEnergy_uniform_bound

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SecondPassArithmetic
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
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S))
    (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (negative : Bool) (b : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative) volume := by
  obtain ⟨M, hM, hb⟩ := secondTotalEnergy_uniform_bound p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H hn negative
  apply b.integrable.norm.mul_bdd (c := M)
  · exact (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H hc negative).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative)]
      exact hb t)
end OAI.SecondPassArithmetic
