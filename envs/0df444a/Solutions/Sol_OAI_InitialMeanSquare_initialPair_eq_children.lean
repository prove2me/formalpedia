-- Prove2me | solution 1 for OAI.InitialMeanSquare.initialPair_eq_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:56:42.344968+00:00
-- url     : https://prove2.me/submissions/fd9548f9-a903-4968-8a9a-4e87b967baf1

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Theorems.Thm_OAI_InitialMeanSquare_initialPair_eq
import Theorems.Thm_OAI_InitialMeanSquare_childSum_eq
import Theorems.Thm_OAI_SecondPassArithmetic_secondActualPair_eq_children


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
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open MixedCrossSeparation (columnCoefficient)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.InitialMeanSquare.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
namespace OAI.InitialMeanSquare
theorem _root_.solution (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) :
    initialPair p hp hg hinj F Ψ₁ Ψ₂ b d h H₁ H₂=
      ∑z : SecondRayIndex,∑V∈F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ b 1 1 1 d h (z,V)*
        star (childSum p hp hcop hg F V (secondRayMinus Ψ₁ z) b d h H₁)*
        childSum p hp hcop hg F V (secondRayPlus Ψ₂ z) b d (-h) H₂ := by
  simp_rw [initialPair_eq p hp hg,childSum_eq p hp hcop hg]
  exact secondActualPair_eq_children p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ b 1 1 1 d h H₁ H₂
end OAI.InitialMeanSquare
