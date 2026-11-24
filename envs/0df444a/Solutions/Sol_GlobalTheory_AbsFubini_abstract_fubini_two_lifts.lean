-- Prove2me | solution 1 for GlobalTheory.AbsFubini.abstract_fubini_two_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:37:04.688891+00:00
-- url     : https://prove2.me/submissions/fdc68979-1a69-46cb-aa07-4e5cd01c22e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralKernelLiftsFubiniSigmaFinite
import Theorems.Thm_GlobalTheory_AbsFubini_lintegral_prod_split
import Theorems.Thm_GlobalTheory_AbsFubini_core
import Theorems.Thm_GlobalTheory_AbsFubini_memLp_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ENNReal
open GlobalTheory GlobalTheory.AbsFubini
variable {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
namespace GlobalTheory.AbsFubini
theorem _root_.solution : ∀ {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) (ν : Measure Y) [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
    (k₁ : X₁ → Y → ℂ) (k₂ : X₂ → Y → ℂ) (u₁ : X₁ → ℂ) (u₂ : X₂ → ℂ),
    Measurable (Function.uncurry k₁) → Measurable (Function.uncurry k₂) → Measurable u₁ → Measurable u₂ →
    ∀ (N₁ : X₁ → ENNReal) (N₂ : X₂ → ENNReal),
    (∀ x, ∫⁻ y, ‖k₁ x y‖ₑ ^ 2 ∂ν ≤ N₁ x ^ 2) → (∀ x, ∫⁻ y, ‖k₂ x y‖ₑ ^ 2 ∂ν ≤ N₂ x ^ 2) →
    ∫⁻ x, N₁ x * ‖u₁ x‖ₑ ∂μ₁ ≠ ⊤ → ∫⁻ x, N₂ x * ‖u₂ x‖ₑ ∂μ₂ ≠ ⊤ →
    (∀ y, Integrable (fun x => k₁ x y * u₁ x) μ₁) → (∀ y, Integrable (fun x => k₂ x y * u₂ x) μ₂) →
    MemLp (fun y => ∫ x, k₁ x y * u₁ x ∂μ₁) 2 ν ∧ MemLp (fun y => ∫ x, k₂ x y * u₂ x ∂μ₂) 2 ν ∧
    ∫ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) ∂ν =
      ∫ p : X₁ × X₂, (∫ y, k₁ p.1 y * conj (k₂ p.2 y) ∂ν) * u₁ p.1 * conj (u₂ p.2) ∂μ₁.prod μ₂ := by
  intro X₁ X₂ Y _ _ _ μ₁ μ₂ ν _ _ _ k₁ k₂ u₁ u₂ hk₁ hk₂ hu₁ hu₂ N₁ N₂ hN₁ hN₂ hf₁ hf₂ _ _
  refine ⟨memLp_lift hk₁ hu₁ hN₁ hf₁, memLp_lift hk₂ hu₂ hN₂ hf₂, ?_⟩
  set F : Y → X₁ × X₂ → ℂ := fun y p => k₁ p.1 y * u₁ p.1 * conj (k₂ p.2 y * u₂ p.2) with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    have e₁ : Measurable fun z : Y × (X₁ × X₂) => k₁ z.2.1 z.1 * u₁ z.2.1 :=
      (hk₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).mul
        (hu₁.comp (measurable_fst.comp measurable_snd))
    have e₂ : Measurable fun z : Y × (X₁ × X₂) => k₂ z.2.2 z.1 * u₂ z.2.2 :=
      (hk₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).mul
        (hu₂.comp (measurable_snd.comp measurable_snd))
    exact e₁.mul (Complex.continuous_conj.measurable.comp e₂)
  have hA₁ : Measurable (Function.uncurry fun x y => ‖k₁ x y‖ₑ) := hk₁.enorm
  have hA₂ : Measurable (Function.uncurry fun x y => ‖k₂ x y‖ₑ) := hk₂.enorm
  have hc := core (μ₁ := μ₁) (μ₂ := μ₂) (ν := ν) hA₁ hA₂ hu₁.enorm hu₂.enorm hN₁ hN₂
  have hFi : Integrable (Function.uncurry F) (ν.prod (μ₁.prod μ₂)) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.enorm.aemeasurable]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hc
      (ENNReal.mul_lt_top hf₁.lt_top hf₂.lt_top))
    refine lintegral_congr fun y => ?_
    have hA₁' : Measurable (Function.uncurry fun x y => ‖k₁ x y‖ₑ * ‖u₁ x‖ₑ) :=
      hA₁.mul (hu₁.enorm.comp measurable_fst)
    have hA₂' : Measurable (Function.uncurry fun x y => ‖k₂ x y‖ₑ * ‖u₂ x‖ₑ) :=
      hA₂.mul (hu₂.enorm.comp measurable_fst)
    rw [lintegral_prod_split (μ₁ := μ₁) (μ₂ := μ₂) hA₁' hA₂' y]
    refine lintegral_congr fun p => ?_
    simp only [Function.uncurry_apply_pair, hFdef, enorm_mul, RCLike.enorm_conj]
  have hpt : ∀ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) =
      ∫ p, F y p ∂μ₁.prod μ₂ := by
    intro y
    rw [← integral_conj]
    exact (integral_prod_mul (fun x => k₁ x y * u₁ x) (fun x => conj (k₂ x y * u₂ x))).symm
  simp_rw [hpt]
  rw [integral_integral_swap hFi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hFdef]
  have : ∀ y, k₁ p.1 y * u₁ p.1 * conj (k₂ p.2 y * u₂ p.2) =
      k₁ p.1 y * conj (k₂ p.2 y) * (u₁ p.1 * conj (u₂ p.2)) := by
    intro y; simp only [map_mul]; ring
  simp_rw [this]
  rw [integral_mul_const]
  ring
end GlobalTheory.AbsFubini
