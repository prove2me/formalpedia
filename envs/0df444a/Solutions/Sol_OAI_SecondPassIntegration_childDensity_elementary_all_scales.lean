-- Prove2me | solution 1 for OAI.SecondPassIntegration.childDensity_elementary_all_scales
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:58:44.931906+00:00
-- url     : https://prove2.me/submissions/91a01a3c-0c67-495c-9e37-27507ea980ce

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Theorems.Thm_OAI_SecondPassIntegration_densityChildEnergy_subunit
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_nonneg
import Theorems.Thm_OAI_SecondPassIntegration_childDensity_elementary_supported


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
open scoped BigOperators Classical
open MeasureTheory
open OAI.SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassIntegration.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassIntegration
theorem _root_.solution
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      (6*128^4*(Real.exp A*M)^2*(∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3)*K*X := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · exact childDensity_elementary_supported p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X F K A M J hX hF hK hA hM hscale hV₁ hV₂ hVs₁ hVs₂ hT
  · rw [densityChildEnergy_subunit p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X A (2*J) hX hVs₁ (lt_of_not_ge hscale),zero_div]
    have hI : 0 ≤ ∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t :=
      integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
    positivity
end OAI.SecondPassIntegration
