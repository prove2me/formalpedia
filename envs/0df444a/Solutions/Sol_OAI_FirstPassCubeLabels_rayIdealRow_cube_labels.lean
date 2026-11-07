-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.rayIdealRow_cube_labels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:14:44.086483+00:00
-- url     : https://prove2.me/submissions/926b7595-f3ab-4ff8-a735-0a32161864dc

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Theorems.Thm_OAI_FirstPassCubeLabels_rayIdealRow_beforeDilation
import Theorems.Thm_OAI_FirstPassCubeLabels_cubeLogCoefficient_originalLabel

set_option autoImplicit false
open OAI
noncomputable section
open OAI.FirstPassCubeLabels
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
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : O) :
    rayIdealRow p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d) negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
      dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
        negative χ p B v ε₁ ε₂ c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂) := by
  have he : cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d =
    fun S => cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f S := by
    funext S
    exact cubeLogCoefficient_originalLabel p hp hcop hg B v ε₁ ε₂ negative C V y t c d f S
  rw [he]
  exact rayIdealRow_beforeDilation p hinj hg F D _ negative χ p B v ε₁ ε₂ hv negative c d f h
end OAI.FirstPassCubeLabels
