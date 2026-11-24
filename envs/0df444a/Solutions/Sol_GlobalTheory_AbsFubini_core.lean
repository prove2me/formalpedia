-- Prove2me | solution 1 for GlobalTheory.AbsFubini.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:06:56.86078+00:00
-- url     : https://prove2.me/submissions/db586994-91d8-497f-b7cb-554ef59bf28d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralKernelLiftsFubiniSigmaFinite
import Theorems.Thm_GlobalTheory_AbsFubini_lintegral_mul_le_sqrt
import Theorems.Thm_GlobalTheory_AbsFubini_sqrt_le_of_sq_le
import Theorems.Thm_GlobalTheory_AbsFubini_lintegral_prod_split

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
theorem _root_.solution {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞} {b₁ : X₁ → ℝ≥0∞} {b₂ : X₂ → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂))
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) {N₁ : X₁ → ℝ≥0∞} {N₂ : X₂ → ℝ≥0∞}
    (hN₁ : ∀ x, ∫⁻ y, a₁ x y ^ 2 ∂ν ≤ N₁ x ^ 2) (hN₂ : ∀ x, ∫⁻ y, a₂ x y ^ 2 ∂ν ≤ N₂ x ^ 2) :
    ∫⁻ y, (∫⁻ x₁, a₁ x₁ y * b₁ x₁ ∂μ₁) * (∫⁻ x₂, a₂ x₂ y * b₂ x₂ ∂μ₂) ∂ν ≤
      (∫⁻ x, N₁ x * b₁ x ∂μ₁) * (∫⁻ x, N₂ x * b₂ x ∂μ₂) := by
  have hA₁ : Measurable (Function.uncurry fun x y => a₁ x y * b₁ x) :=
    ha₁.mul (hb₁.comp measurable_fst)
  have hA₂ : Measurable (Function.uncurry fun x y => a₂ x y * b₂ x) :=
    ha₂.mul (hb₂.comp measurable_fst)

  set n₁ : X₁ → ℝ≥0∞ := fun x => (∫⁻ y, a₁ x y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) with hn₁
  set n₂ : X₂ → ℝ≥0∞ := fun x => (∫⁻ y, a₂ x y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) with hn₂
  have mn₁ : Measurable n₁ :=
    ((ha₁.pow_const (2:ℝ)).lintegral_prod_right' (ν := ν)).pow_const _
  have mn₂ : Measurable n₂ :=
    ((ha₂.pow_const (2:ℝ)).lintegral_prod_right' (ν := ν)).pow_const _
  have nN₁ : ∀ x, n₁ x ≤ N₁ x := fun x => sqrt_le_of_sq_le (by simpa [ENNReal.rpow_two] using hN₁ x)
  have nN₂ : ∀ x, n₂ x ≤ N₂ x := fun x => sqrt_le_of_sq_le (by simpa [ENNReal.rpow_two] using hN₂ x)
  have hsplit := lintegral_prod_split (μ₁ := μ₁) (μ₂ := μ₂) hA₁ hA₂
  simp only [hsplit]
  have hG : Measurable (Function.uncurry fun (y : Y) (p : X₁ × X₂) =>
      a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2)) := by
    have e₁ : Measurable fun z : Y × (X₁ × X₂) => a₁ z.2.1 z.1 * b₁ z.2.1 :=
      hA₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
    have e₂ : Measurable fun z : Y × (X₁ × X₂) => a₂ z.2.2 z.1 * b₂ z.2.2 :=
      hA₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
    exact e₁.mul e₂
  rw [lintegral_lintegral_swap hG.aemeasurable]
  calc ∫⁻ p : X₁ × X₂, ∫⁻ y, a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2) ∂ν ∂μ₁.prod μ₂
      ≤ ∫⁻ p : X₁ × X₂, (n₁ p.1 * b₁ p.1) * (n₂ p.2 * b₂ p.2) ∂μ₁.prod μ₂ := by
        refine lintegral_mono fun p => ?_
        have m₁ : Measurable fun y => a₁ p.1 y := ha₁.comp (measurable_const.prodMk measurable_id)
        have m₂ : Measurable fun y => a₂ p.2 y := ha₂.comp (measurable_const.prodMk measurable_id)
        calc ∫⁻ y, a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2) ∂ν
            = ∫⁻ y, (b₁ p.1 * b₂ p.2) * (a₁ p.1 y * a₂ p.2 y) ∂ν := by
              congr 1; funext y; ring
          _ = (b₁ p.1 * b₂ p.2) * ∫⁻ y, a₁ p.1 y * a₂ p.2 y ∂ν := lintegral_const_mul _ (m₁.mul m₂)
          _ ≤ (b₁ p.1 * b₂ p.2) * (n₁ p.1 * n₂ p.2) :=
              by gcongr; exact lintegral_mul_le_sqrt ν m₁ m₂
          _ = (n₁ p.1 * b₁ p.1) * (n₂ p.2 * b₂ p.2) := by ring
    _ = (∫⁻ x, n₁ x * b₁ x ∂μ₁) * (∫⁻ x, n₂ x * b₂ x ∂μ₂) :=
        lintegral_prod_mul (f := fun x => n₁ x * b₁ x) (g := fun x => n₂ x * b₂ x)
          (mn₁.mul hb₁).aemeasurable (mn₂.mul hb₂).aemeasurable
    _ ≤ (∫⁻ x, N₁ x * b₁ x ∂μ₁) * (∫⁻ x, N₂ x * b₂ x ∂μ₂) :=
        by
          gcongr with x x
          · exact nN₁ x
          · exact nN₂ x
end GlobalTheory.AbsFubini
