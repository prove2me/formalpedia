-- Prove2me | solution 1 for MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/205ce375-3f66-5bbd-9650-2b02d0096877

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace JensenL2Proof

variable {A : Type*} [MeasurableSpace A]

private theorem enorm_integral_mul_sq_le (ρ : Measure A) (p : A → ℝ) (hp : Measurable p) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∫⁻ a, ENNReal.ofReal (p a) ∂ρ = 1) (G : A → ℂ) (hG : AEStronglyMeasurable G ρ) :
    ‖∫ a, G a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ≤ ∫⁻ a, ENNReal.ofReal (p a) * ‖G a‖ₑ ^ 2 ∂ρ := by

  set w : A → ℝ≥0∞ := fun a => ENNReal.ofReal (p a) with hw
  have hwm : Measurable w := hp.ennreal_ofReal
  have hGm : AEMeasurable (fun a => ‖G a‖ₑ) ρ := hG.enorm

  have h1 : ‖∫ a, G a * (p a : ℂ) ∂ρ‖ₑ ≤ ∫⁻ a, ‖G a‖ₑ * w a ∂ρ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun a => ?_
    rw [enorm_mul, hw]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 a)]

  have h2 : ∫⁻ a, ‖G a‖ₑ * w a ∂ρ ≤ (∫⁻ a, w a * ‖G a‖ₑ ^ 2 ∂ρ) ^ (1 / 2 : ℝ) := by
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two
      (f := fun a => ‖G a‖ₑ * w a ^ (1 / 2 : ℝ)) (g := fun a => w a ^ (1 / 2 : ℝ))
      (hGm.mul (hwm.pow_const _).aemeasurable) (hwm.pow_const _).aemeasurable
    have hfg : (fun a => ‖G a‖ₑ * w a ^ (1 / 2 : ℝ)) * (fun a => w a ^ (1 / 2 : ℝ)) = fun a => ‖G a‖ₑ * w a := by
      funext a
      simp only [Pi.mul_apply]
      rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    have hf2 : ∀ a, (‖G a‖ₑ * w a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = w a * ‖G a‖ₑ ^ 2 := by
      intro a
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul]
      norm_num
      rw [mul_comm]
    have hg2 : ∀ a, (w a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = w a := by
      intro a
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [hfg] at hH
    simp_rw [hf2, hg2] at hH
    rw [hp1, ENNReal.one_rpow, mul_one] at hH
    exact hH

  calc ‖∫ a, G a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ≤ ((∫⁻ a, w a * ‖G a‖ₑ ^ 2 ∂ρ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' (h1.trans h2) 2
    _ = ∫⁻ a, w a * ‖G a‖ₑ ^ 2 ∂ρ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

end JensenL2Proof

open JensenL2Proof in
theorem solution
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (ν : Measure X) (ρ : Measure A) [SFinite ν] [SFinite ρ]
    (p : A → ℝ) (hp : Measurable p) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∫ a, p a ∂ρ = 1)
    (u : X → ℂ) (hu : Measurable u) (U : X → A → ℂ) (hU : Measurable (Function.uncurry U))
    (hint : ∀ x, Integrable (fun a => U x a * (p a : ℂ)) ρ) :
    ∫⁻ x, ‖u x - ∫ a, U x a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ x, ‖u x - U x a‖ₑ ^ 2 ∂ν ∂ρ := by

  have hpi : Integrable p ρ := Integrable.of_integral_ne_zero (by rw [hp1]; exact one_ne_zero)
  have hp1' : ∫⁻ a, ENNReal.ofReal (p a) ∂ρ = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hpi (ae_of_all _ hp0), hp1, ENNReal.ofReal_one]

  have hpt : ∀ x, ‖u x - ∫ a, U x a * (p a : ℂ) ∂ρ‖ₑ ^ 2
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ‖u x - U x a‖ₑ ^ 2 ∂ρ := by
    intro x
    have hux : u x = ∫ a, u x * (p a : ℂ) ∂ρ := by
      rw [integral_const_mul, integral_complex_ofReal, hp1, Complex.ofReal_one, mul_one]
    have hsub : u x - ∫ a, U x a * (p a : ℂ) ∂ρ = ∫ a, (u x - U x a) * (p a : ℂ) ∂ρ := by
      have hpc : Integrable (fun a => (p a : ℂ)) ρ := hpi.ofReal (𝕜 := ℂ)
      conv_lhs => rw [hux]
      rw [← integral_sub (hpc.const_mul (u x)) (hint x)]
      refine integral_congr_ae (ae_of_all _ fun a => ?_)
      ring
    rw [hsub]
    have hGx : AEStronglyMeasurable (fun a => u x - U x a) ρ :=
      (aestronglyMeasurable_const.sub (hU.of_uncurry_left.aestronglyMeasurable))
    exact enorm_integral_mul_sq_le ρ p hp hp0 hp1' _ hGx

  calc ∫⁻ x, ‖u x - ∫ a, U x a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ x, ∫⁻ a, ENNReal.ofReal (p a) * ‖u x - U x a‖ₑ ^ 2 ∂ρ ∂ν := lintegral_mono hpt
    _ = ∫⁻ a, ∫⁻ x, ENNReal.ofReal (p a) * ‖u x - U x a‖ₑ ^ 2 ∂ν ∂ρ := by
        refine lintegral_lintegral_swap ?_
        refine ((hp.ennreal_ofReal.comp measurable_snd).mul ?_).aemeasurable
        exact ((hu.comp measurable_fst).sub hU).enorm.pow_const 2
    _ = ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ x, ‖u x - U x a‖ₑ ^ 2 ∂ν ∂ρ := by
        refine lintegral_congr fun a => ?_
        rw [lintegral_const_mul]
        exact ((hu.sub hU.of_uncurry_right).enorm.pow_const 2)

end S_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq
end P2MW
export P2MW.S_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq (solution)
