-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalTwoPassage_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:04:35.100767+00:00
-- url     : https://prove2.me/submissions/e42b7f0f-f84f-4680-887d-f6772686cf21

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SquarefreeTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Theorems.Thm_OAI_SecondPassArithmetic_globalCubeInputFamilyEnergy_transfer
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstPooledRow_side
import Theorems.Thm_OAI_SecondPassArithmetic_globalCubeFirstBlock_input_transfer

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Ct₁ C₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H Ymax : ℝ),
      0≤Γ → 0<K → 0<ell → 0<B → 0<F → 0≤H → 0≤Ymax →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*Ymax^deltaLoss*
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₁ m₁ g₁ V₁ windows₁ C₁ Ct₁ Γ ε K ell B F M₁ H A J N true) *
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₂ m₂ g₂ V₂ windows₂ C₂ Ct₂ Γ ε K ell B F M₂ H A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := globalCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Ct₁,hC₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ := globalCubeInputFamilyEnergy_transfer ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Ct₂,hC₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ := globalCubeInputFamilyEnergy_transfer ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Ct₁,C₂,Ct₂,hCfirst,hC₁,hCt₁,hC₂,hCt₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H Ymax
    hΓ hK hell hB hF hH hYmax0 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hYmax hsf hs0 hmap hT0 hT
  have hf := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax
    hK hell hB hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha hYmax hsf hs0 hmap hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H Ψ₁ m₁ T hΓ hw hK hell hB hF hH hadm hΨ₁ hb₁ hb₂ hT hT0
  have hT' : ∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
      globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    intro b hb z hz
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H Ψ₂ m₂ T hΓ hw hK hell hB hF hH hadm hΨ₂ hb₁ hb₂ hT' hT0
  have hprefix : 0≤Cfirst*Ymax^deltaLoss := mul_nonneg hCfirst (Real.rpow_nonneg hYmax0 _)
  apply hf.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _))
end OAI.SecondPassArithmetic
