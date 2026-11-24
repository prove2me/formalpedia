-- Prove2me | solution 1 for GlobalTheory.CoinvSB.kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:18:05.253319+00:00
-- url     : https://prove2.me/submissions/27de9a5e-8e7f-4c25-9d04-6efac2a9d0d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralLastFactorSliceMemSchwartzBruhatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsCutoffOfAddCharTranslationInvariantFunctioStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatFunctionalZeroOfFibreIntegralZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional
import Theorems.Thm_GlobalTheory_SBConv_eventually_translate
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_T_exists_cutoff_of_addChar_translation_invariant_functional
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_functional_zero_of_fibre_integral_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CoinvSB
namespace GlobalTheory.CoinvSB
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ D : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀, ∫ a, D.1 (x₀, 0, a) ∂(Measure.pi fun _ => ν) = 0) → l D = 0 := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2 D hD
  obtain ⟨s, hs⟩ : ∃ s : kˣ, ∀ t ∈ box I₁ s, ∀ y : (I₀ → k) × (I₁ → k) × (I₂ → k),
      D.1 (y + (0, t, 0)) = D.1 y := by
    have h := GlobalTheory.SBConv.eventually_translate D.2
    have hT : Filter.Tendsto (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) := by fun_prop
      exact this.tendsto' 0 0 (by simp)
    obtain ⟨s, hs⟩ := exists_box_subset (hT.eventually h)
    refine ⟨s, fun t ht y => ?_⟩
    have := hs ht y
    simpa [sub_eq_add_neg] using this
  obtain ⟨Φ', hΦ', hl⟩ := GlobalTheory.T.exists_cutoff_of_addChar_translation_invariant_functional k ψ hψc hψ1 I₀ I₁ I₂ M l h1 D s
  have hz : ∀ x₀ x₁, ∫ a, Φ'.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0 := by
    intro x₀ x₁
    simp_rw [hΦ']
    by_cases hx : x₁ ∈ box I₁ s
    · have e : ∀ a, D.1 (x₀, x₁, a) = D.1 (x₀, 0, a) := fun a => by
        simpa using hs x₁ hx (x₀, 0, a)
      simp only [Set.indicator_of_mem hx, one_mul, e]
      exact hD x₀
    · simp [Set.indicator_of_notMem hx]
  rw [hl]
  exact GlobalTheory.T.schwartzBruhat_functional_zero_of_fibre_integral_zero k ν hν I₀ I₁ I₂ M l h2 Φ' hz
end GlobalTheory.CoinvSB
