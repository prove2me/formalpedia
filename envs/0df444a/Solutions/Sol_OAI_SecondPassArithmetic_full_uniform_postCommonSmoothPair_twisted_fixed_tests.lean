-- Prove2me | solution 1 for OAI.SecondPassArithmetic.full_uniform_postCommonSmoothPair_twisted_fixed_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:31:30.797558+00:00
-- url     : https://prove2.me/submissions/589c1b40-4dbd-48fc-a9be-5466e1ba81b9

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_UniformTransfer
import Theorems.Thm_OAI_JointLogSeparation_seven_kernel_twisted_profiles
import Theorems.Thm_OAI_SecondPassArithmetic_postCommonSmoothPair_fixed_tests


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
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ, (1+R)^A * ‖(𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) t₁ * (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
        C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
        (z ud ue uv kap X₁ X₂ : ℝ),
        postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V
          z ud ue uv kap X₁ X₂ R =
        separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) b V
          z ud ue uv kap X₁ X₂ := by
  obtain ⟨C, hC, hsep⟩ := JointLogSeparation.seven_kernel_twisted_profiles A₁ A₂ W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb⟩ := hsep R hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  obtain ⟨hid, hpoint, hint⟩ := hb θ₁ θ₂
  refine ⟨hpoint, ?_⟩
  intro ι _ p hp _ hcop hg
    F Ψ₁ Ψ₂ m f y₁ y₂ z ud ue uv kap X₁ X₂
  exact postCommonSmoothPair_fixed_tests p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V
    z ud ue uv kap X₁ X₂ R b (hid z ud ue uv kap)
end OAI.SecondPassArithmetic
