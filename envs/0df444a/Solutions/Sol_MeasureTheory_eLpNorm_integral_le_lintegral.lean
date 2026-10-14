-- Prove2me | solution 1 for MeasureTheory.eLpNorm_integral_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:50:03.27181+00:00
-- url     : https://prove2.me/submissions/b9da12cb-7228-4e0c-9ec0-b6f5ea7e9903

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Theorems.Thm_MeasureTheory_eLpNorm_lintegral_le_of_lt_top

open MeasureTheory

theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (F : α → β → ℝ)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hFi : ∀ᵐ x ∂μ, Integrable (F x) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
      ∫⁻ y, eLpNorm (fun x => F x y) p μ ∂ν := by
  by_cases hpone : p = 1
  · subst p
    simp_rw [eLpNorm_one_eq_lintegral_enorm]
    calc
      (∫⁻ x, ‖∫ y, F x y ∂ν‖ₑ ∂μ) ≤ ∫⁻ x, ∫⁻ y, ‖F x y‖ₑ ∂ν ∂μ :=
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm (F x)
      _ = ∫⁻ y, ∫⁻ x, ‖F x y‖ₑ ∂μ ∂ν :=
        lintegral_lintegral_swap hF.enorm
  by_cases htop : (∫⁻ y, eLpNorm (fun x => F x y) p μ ∂ν) = ⊤
  · rw [htop]
    exact le_top
  have hpgt : 1 < p := lt_of_le_of_ne hp (Ne.symm hpone)
  have hq : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).2 hpgt
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop
  have hbound : (∫⁻ y, eLpNorm (fun x => ‖F x y‖ₑ) (ENNReal.ofReal p.toReal) μ ∂ν) < ⊤ := by
    simpa only [hpeq, eLpNorm_enorm] using (lt_top_iff_ne_top.mpr htop)
  have hnonneg := MeasureTheory.eLpNorm_lintegral_le_of_lt_top μ ν hq
    (fun x y => ‖F x y‖ₑ) hF.enorm hbound
  simp only [hpeq, eLpNorm_enorm] at hnonneg
  refine le_trans ?_ hnonneg
  apply eLpNorm_mono_enorm
  intro x
  simpa only [enorm_eq_self] using enorm_integral_le_lintegral_enorm (F x)
