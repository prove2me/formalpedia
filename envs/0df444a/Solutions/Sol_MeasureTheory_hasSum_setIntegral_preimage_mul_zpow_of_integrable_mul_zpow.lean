-- Prove2me | solution 1 for MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b31f4bee-db9b-583e-8c3f-648e8d7d18a3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow

set_option autoImplicit false

open MeasureTheory

namespace ShellDecomp

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_const_zpow (c : ℂ) {E : Ω → ℤ} (hE : Measurable E) :
    Measurable fun ω => c ^ E ω :=
  (measurable_of_countable fun n : ℤ => c ^ n).comp hE

theorem measurableSet_fiber {E : Ω → ℤ} (hE : Measurable E) (n : ℤ) :
    MeasurableSet (E ⁻¹' {n}) :=
  hE (measurableSet_singleton n)

omit [MeasurableSpace Ω] in
theorem iUnion_fiber (E : Ω → ℤ) : (⋃ n : ℤ, E ⁻¹' {n}) = Set.univ := by
  ext ω; simp

omit [MeasurableSpace Ω] in

theorem norm_mul_zpow (G : Ω → ℂ) (E : Ω → ℤ) {Y : ℂ} {r : ℝ} (hY : ‖Y‖ = r) (ω : Ω) :
    ‖G ω * Y ^ E ω‖ = ‖G ω‖ * r ^ E ω := by
  rw [norm_mul, norm_zpow, hY]

theorem aestronglyMeasurable_of_mul_zpow (ρ : Measure Ω) {E : Ω → ℤ} (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : AEStronglyMeasurable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    AEStronglyMeasurable G ρ := by
  have hne : ∀ ω, ((r : ℂ) ^ E ω) ≠ 0 := fun ω =>
    zpow_ne_zero _ (by exact_mod_cast hr.ne')
  have h2 : AEStronglyMeasurable (fun ω => ((r : ℂ) ^ E ω)⁻¹) ρ :=
    (measurable_const_zpow (r : ℂ) hE).inv.aestronglyMeasurable
  have := hG.mul h2
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  show G ω * (r : ℂ) ^ E ω * ((r : ℂ) ^ E ω)⁻¹ = G ω
  rw [mul_assoc, mul_inv_cancel₀ (hne ω), mul_one]

theorem integrable_mul_zpow_of_norm_eq (ρ : Measure Ω) {E : Ω → ℤ} (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) {Y : ℂ} (hY : ‖Y‖ = r) :
    Integrable (fun ω => G ω * Y ^ E ω) ρ := by
  have hGm : AEStronglyMeasurable G ρ := aestronglyMeasurable_of_mul_zpow ρ hE G hr hG.1
  have hm : AEStronglyMeasurable (fun ω => G ω * Y ^ E ω) ρ :=
    hGm.mul (measurable_const_zpow Y hE).aestronglyMeasurable
  refine hG.congr' hm (Filter.Eventually.of_forall fun ω => ?_)
  have hr' : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [norm_mul_zpow G E hr', norm_mul_zpow G E hY]

theorem integrable_norm_mul_zpow (ρ : Measure Ω) {E : Ω → ℤ}
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    Integrable (fun ω => ‖G ω‖ * r ^ E ω) ρ := by
  have hr' : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have := hG.norm
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact norm_mul_zpow G E hr' ω

end ShellDecomp

open ShellDecomp in

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) (E : Ω → ℤ) (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, ‖G ω‖ ∂ρ) * r ^ n) (∫ ω, ‖G ω‖ * r ^ E ω ∂ρ) ∧
    (Summable fun n : ℤ => ‖∫ ω in E ⁻¹' {n}, G ω ∂ρ‖ * r ^ n) ∧
    ∀ Y : ℂ, ‖Y‖ = r →
      Integrable (fun ω => G ω * Y ^ E ω) ρ ∧
      HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, G ω ∂ρ) * Y ^ n) (∫ ω, G ω * Y ^ E ω ∂ρ) := by
  have hms : ∀ n : ℤ, MeasurableSet (E ⁻¹' {n}) := measurableSet_fiber hE
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℤ => E ⁻¹' {n}) := pairwise_disjoint_fiber E

  have hreal : HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, ‖G ω‖ ∂ρ) * r ^ n)
      (∫ ω, ‖G ω‖ * r ^ E ω ∂ρ) := by
    have hint : Integrable (fun ω => ‖G ω‖ * r ^ E ω) ρ := integrable_norm_mul_zpow ρ G hr hG
    have h := hasSum_integral_iUnion (μ := ρ) (f := fun ω => ‖G ω‖ * r ^ E ω) hms hdisj
      (by rw [iUnion_fiber]; exact hint.integrableOn)
    rw [iUnion_fiber, Measure.restrict_univ] at h
    refine h.congr_fun fun n => ?_

    have : ∫ ω in E ⁻¹' {n}, ‖G ω‖ * r ^ E ω ∂ρ = ∫ ω in E ⁻¹' {n}, ‖G ω‖ * r ^ n ∂ρ := by
      refine setIntegral_congr_fun (hms n) fun ω hω => ?_
      have hn : E ω = n := by simpa using hω
      simp only [hn]
    rw [this, integral_mul_const]
  refine ⟨hreal, ?_, ?_⟩
  ·
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le n))
      (fun n => ?_) hreal.summable
    exact mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (zpow_nonneg hr.le n)
  ·
    intro Y hY
    have hint : Integrable (fun ω => G ω * Y ^ E ω) ρ := integrable_mul_zpow_of_norm_eq ρ hE G hr hG hY
    refine ⟨hint, ?_⟩
    have h := hasSum_integral_iUnion (μ := ρ) (f := fun ω => G ω * Y ^ E ω) hms hdisj
      (by rw [iUnion_fiber]; exact hint.integrableOn)
    rw [iUnion_fiber, Measure.restrict_univ] at h
    refine h.congr_fun fun n => ?_
    have : ∫ ω in E ⁻¹' {n}, G ω * Y ^ E ω ∂ρ = ∫ ω in E ⁻¹' {n}, G ω * Y ^ n ∂ρ := by
      refine setIntegral_congr_fun (hms n) fun ω hω => ?_
      have hn : E ω = n := by simpa using hω
      simp only [hn]
    rw [this, integral_mul_const]

end S_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
end P2MW
export P2MW.S_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow (solution)
