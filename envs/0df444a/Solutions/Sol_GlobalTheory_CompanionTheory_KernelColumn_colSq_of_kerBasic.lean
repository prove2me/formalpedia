-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelColumn.colSq_of_kerBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:59.217052+00:00
-- url     : https://prove2.me/submissions/56e35b4e-99e7-477c-b70e-8c7d39a5fe22

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColSqOfKerBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumn
namespace GlobalTheory.CompanionTheory.KernelColumn
theorem _root_.solution : KerBasic → ColSq := by
  intro hK X φ B Ω hT hB hΩ hS y
  letI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hker := (hK X φ hT).2.2.2.2.2
  have hBe : ∀ z, ‖φ z‖ₑ ≤ ENNReal.ofReal B := fun z => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hB z)
  let A : X.G → ℝ≥0∞ := fun x => ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ
  have hterm : ∀ γ : X.Γ, Measurable fun x : X.G => ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ := fun γ =>
    (hT.1.comp (by fun_prop)).enorm.measurable
  have hAm : Measurable A := Measurable.ennreal_tsum hterm
  have hAinv : ∀ (δ : X.Γ) (x : X.G), A ((δ : X.G) * x) = A x := by
    intro δ x
    simp only [A]
    rw [← (Equiv.mulLeft δ).tsum_eq (fun γ : X.Γ => ‖φ (((δ : X.G) * x)⁻¹ * (γ : X.G) * y)‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp [mul_assoc]
  let g : X.G → ℝ≥0∞ := fun x => ‖φ (x⁻¹ * y)‖ₑ * A x
  have hgm : Measurable g :=
    ((hT.1.comp (by fun_prop : Continuous fun x : X.G => x⁻¹ * y)).enorm.measurable).mul hAm
  have hsq : ∀ x, A x ^ 2 = ∑' γ : X.Γ, g (γ⁻¹ • x) := by
    intro x
    rw [sq]
    calc A x * A x = (∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ) * A x := rfl
      _ = ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ * A x := ENNReal.tsum_mul_right.symm
      _ = ∑' γ : X.Γ, g (γ⁻¹ • x) := by
        refine tsum_congr fun γ => ?_
        have e : γ⁻¹ • x = ((γ⁻¹ : X.Γ) : X.G) * x := rfl
        simp only [g]
        rw [e, hAinv]
        simp [mul_assoc]
  let c : ℝ≥0∞ := ENNReal.ofReal B * (ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y)
  have hg : ∀ x, g x ≤ (y • Ω⁻¹).indicator (fun _ => c) x := by
    intro x
    by_cases h0 : φ (x⁻¹ * y) = 0
    · simp [g, h0]
    · have hω : x⁻¹ * y ∈ Ω := hS h0
      have hx : x ∈ y • Ω⁻¹ := by
        rw [Set.mem_smul_set]
        exact ⟨y⁻¹ * x, by simpa [Set.mem_inv] using hω, by simp⟩
      rw [Set.indicator_of_mem hx]
      have h2 : A x ≤ ENNReal.ofReal B * cnt X.Γ (Ω⁻¹ * Ω) y := by
        simp only [A, cnt]
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases h3 : φ (x⁻¹ * (γ : X.G) * y) = 0
        · simp [h3]
        · have hm : y⁻¹ * (γ : X.G) * y ∈ Ω⁻¹ * Ω :=
            Set.mem_mul.2 ⟨(x⁻¹ * y)⁻¹, Set.inv_mem_inv.2 hω, x⁻¹ * (γ : X.G) * y, hS h3, by group⟩
          rw [Set.indicator_of_mem hm]
          simpa using hBe _
      exact mul_le_mul' (hBe _) h2
  calc ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ^ 2 ∂X.ν ≤ ∫⁻ x, A x ^ 2 ∂X.ν :=
        lintegral_mono fun x => pow_le_pow_left' (hker x y) 2
    _ = ∫⁻ x in X.F, ∑' γ : X.Γ, g (γ⁻¹ • x) ∂X.μ := by
        simp only [hsq]; rfl
    _ = ∑' γ : X.Γ, ∫⁻ x in X.F, g (γ⁻¹ • x) ∂X.μ :=
        lintegral_tsum fun γ => (hgm.comp (measurable_const_mul ((γ⁻¹ : X.Γ) : X.G))).aemeasurable
    _ = ∫⁻ x, g x ∂X.μ := (X.fd.lintegral_eq_tsum' g).symm
    _ ≤ ∫⁻ x, (y • Ω⁻¹).indicator (fun _ => c) x ∂X.μ := lintegral_mono hg
    _ ≤ c * X.μ (y • Ω⁻¹) := lintegral_indicator_const_le _ _
    _ = ENNReal.ofReal B ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y := by
        rw [measure_smul]
        simp only [c]
        ring
end GlobalTheory.CompanionTheory.KernelColumn
