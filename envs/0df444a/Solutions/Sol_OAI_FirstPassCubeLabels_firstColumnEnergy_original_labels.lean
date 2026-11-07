-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.firstColumnEnergy_original_labels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:22:53.802796+00:00
-- url     : https://prove2.me/submissions/26b020be-6d90-47c4-8d0c-2b1077bc1fa6

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Theorems.Thm_OAI_FirstPassCubeLabels_rayIdealRow_cube_labels
import Theorems.Thm_OAI_FirstPassCubeLabels_normalized_originalLabelColumn

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
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V X d h b =
    ∫ t : ℝ, ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
        ‖rayPairWeight p r D h‖ *
        (‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D‖ ^ 2 *
          ‖dilatedRayColumn p hg F D
            (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative
              (normalizedColumn p C) V (columnLog p X) t)
            negative (if negative then r.1 else r.2) p B v ε₁ ε₂ c d
            (h * f ^ 2 * dilationLabel p B v ε₁ ε₂)‖ ^ 2) := by
  unfold firstColumnEnergy
  rw [normalized_originalLabelColumn]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  unfold rayIdealEnergy
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  rw [rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv negative _
    (normalizedColumn p C) V (columnLog p X) t c d f h, norm_mul, mul_pow]
end OAI.FirstPassCubeLabels
