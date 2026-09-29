-- Prove2me | solution 1 for MeasureTheory.memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/fddd0426-ddb7-53e9-9266-d14bbf8524c1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul

set_option autoImplicit false

open MeasureTheory

open scoped ENNReal

namespace L2PacketBoundAux

theorem rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem measurable_weight : Measurable (fun t : ℝ => ENNReal.ofReal (1 + t ^ 2)) :=
  ENNReal.measurable_ofReal.comp (continuous_const.add (continuous_id.pow 2)).measurable

theorem enorm_integral_sq_le (φ : ℝ → ℂ) (hφ : AEStronglyMeasurable φ volume) :
    ‖∫ t, φ t‖ₑ ^ 2 ≤ ENNReal.ofReal Real.pi * ∫⁻ t, ENNReal.ofReal (1 + t ^ 2) * ‖φ t‖ₑ ^ 2 := by
  have hw0 : ∀ t : ℝ, ENNReal.ofReal (1 + t ^ 2) ≠ 0 := fun t =>
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hfg : (fun t : ℝ => ‖φ t‖ₑ)
      = (fun t : ℝ => ENNReal.ofReal (1 + t ^ 2) ^ (-(1 / 2 : ℝ)))
        * (fun t : ℝ => ENNReal.ofReal (1 + t ^ 2) ^ (1 / 2 : ℝ) * ‖φ t‖ₑ) := by
    funext t
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.rpow_add _ _ (hw0 t) ENNReal.ofReal_ne_top]
    norm_num
  have hfm : AEMeasurable (fun t : ℝ => ENNReal.ofReal (1 + t ^ 2) ^ (-(1 / 2 : ℝ))) volume :=
    (measurable_weight.pow_const _).aemeasurable
  have hgm : AEMeasurable (fun t : ℝ => ENNReal.ofReal (1 + t ^ 2) ^ (1 / 2 : ℝ) * ‖φ t‖ₑ) volume :=
    (measurable_weight.pow_const _).aemeasurable.mul hφ.enorm
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hfm hgm
  have hf2 : ∫⁻ t : ℝ, (ENNReal.ofReal (1 + t ^ 2) ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) = ENNReal.ofReal Real.pi := by
    have e : ∀ t : ℝ, (ENNReal.ofReal (1 + t ^ 2) ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ)
        = ENNReal.ofReal ((1 + t ^ 2)⁻¹) := fun t => by
      rw [← ENNReal.rpow_mul, ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.rpow_neg_one]
      norm_num
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
      (Filter.Eventually.of_forall fun t => by positivity), integral_univ_inv_one_add_sq]
  have hg2 : ∫⁻ t : ℝ, (ENNReal.ofReal (1 + t ^ 2) ^ (1 / 2 : ℝ) * ‖φ t‖ₑ) ^ (2 : ℝ)
      = ∫⁻ t : ℝ, ENNReal.ofReal (1 + t ^ 2) * ‖φ t‖ₑ ^ 2 := by
    refine lintegral_congr fun t => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  calc ‖∫ t, φ t‖ₑ ^ 2 ≤ (∫⁻ t, ‖φ t‖ₑ) ^ 2 := by
        gcongr
        exact enorm_integral_le_lintegral_enorm φ
    _ = (∫⁻ t, ((fun t : ℝ => ENNReal.ofReal (1 + t ^ 2) ^ (-(1 / 2 : ℝ)))
          * (fun t : ℝ => ENNReal.ofReal (1 + t ^ 2) ^ (1 / 2 : ℝ) * ‖φ t‖ₑ)) t) ^ 2 := by
        rw [← hfg]
    _ ≤ ((∫⁻ t : ℝ, (ENNReal.ofReal (1 + t ^ 2) ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
          * (∫⁻ t : ℝ, (ENNReal.ofReal (1 + t ^ 2) ^ (1 / 2 : ℝ) * ‖φ t‖ₑ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
    _ = (∫⁻ t : ℝ, (ENNReal.ofReal (1 + t ^ 2) ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ))
          * (∫⁻ t : ℝ, (ENNReal.ofReal (1 + t ^ 2) ^ (1 / 2 : ℝ) * ‖φ t‖ₑ) ^ (2 : ℝ)) := by
        rw [mul_pow, rpow_half_sq, rpow_half_sq]
    _ = ENNReal.ofReal Real.pi * ∫⁻ t, ENNReal.ofReal (1 + t ^ 2) * ‖φ t‖ₑ ^ 2 := by
        rw [hf2, hg2]

end L2PacketBoundAux

open L2PacketBoundAux in
theorem solution
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (G : ℝ × X → ℂ) (_hG : AEStronglyMeasurable G ((volume : Measure ℝ).prod μ))
    (M : ℝ → ℝ) (_hM0 : ∀ t, 0 ≤ M t)
    (_hGt : ∀ t : ℝ, MemLp (fun x => G (t, x)) 2 μ ∧ (∫ x, ‖G (t, x)‖ ^ 2 ∂μ) ≤ M t)
    (_hM : Integrable (fun t : ℝ => (1 + t ^ 2) * M t)) :
    MemLp (fun x => ∫ t : ℝ, G (t, x)) 2 μ ∧
    (∫ x, ‖∫ t : ℝ, G (t, x)‖ ^ 2 ∂μ) ≤ Real.pi * ∫ t : ℝ, (1 + t ^ 2) * M t := by
  have hGs : AEStronglyMeasurable (fun z : X × ℝ => G z.swap) (μ.prod volume) := _hG.prod_swap
  have hmeas : AEStronglyMeasurable (fun x => ∫ t : ℝ, G (t, x)) μ := hGs.integral_prod_right'
  have hsec : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun t : ℝ => G (t, x)) volume := hGs.prodMk_left

  have hpt : ∀ᵐ x ∂μ, ‖∫ t : ℝ, G (t, x)‖ₑ ^ 2
      ≤ ENNReal.ofReal Real.pi * ∫⁻ t : ℝ, ENNReal.ofReal (1 + t ^ 2) * ‖G (t, x)‖ₑ ^ 2 :=
    hsec.mono fun x hx => enorm_integral_sq_le (fun t => G (t, x)) hx

  have hslice : ∀ t : ℝ, ∫⁻ x, ‖G (t, x)‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (M t) := by
    intro t
    obtain ⟨hmem, hle⟩ := _hGt t
    have hint : Integrable (fun x => ‖G (t, x)‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    have e : ∫⁻ x, ‖G (t, x)‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖G (t, x)‖ ^ 2 ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity)]
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [e]
    exact ENNReal.ofReal_le_ofReal hle

  have hmeas2 : AEMeasurable (Function.uncurry fun (x : X) (t : ℝ) =>
      ENNReal.ofReal (1 + t ^ 2) * ‖G (t, x)‖ₑ ^ 2) (μ.prod volume) := by
    have h1 : AEMeasurable (fun z : X × ℝ => ‖G z.swap‖ₑ ^ 2) (μ.prod volume) := hGs.enorm.pow_const 2
    have h2 : Measurable (fun z : X × ℝ => ENNReal.ofReal (1 + z.2 ^ 2)) :=
      measurable_weight.comp measurable_snd
    exact h2.aemeasurable.mul h1
  have htot : (∫⁻ x, (∫⁻ t : ℝ, ENNReal.ofReal (1 + t ^ 2) * ‖G (t, x)‖ₑ ^ 2) ∂μ)
      ≤ ENNReal.ofReal (∫ t : ℝ, (1 + t ^ 2) * M t) := by
    rw [lintegral_lintegral_swap hmeas2]
    calc ∫⁻ t : ℝ, (∫⁻ x, ENNReal.ofReal (1 + t ^ 2) * ‖G (t, x)‖ₑ ^ 2 ∂μ)
        = ∫⁻ t : ℝ, ENNReal.ofReal (1 + t ^ 2) * (∫⁻ x, ‖G (t, x)‖ₑ ^ 2 ∂μ) := by
          refine lintegral_congr fun t => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal (1 + t ^ 2) * ENNReal.ofReal (M t) :=
          lintegral_mono fun t => by dsimp only; gcongr; exact hslice t
      _ = ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2) * M t) := by
          refine lintegral_congr fun t => ?_
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (∫ t : ℝ, (1 + t ^ 2) * M t) :=
          (ofReal_integral_eq_lintegral_ofReal _hM
            (Filter.Eventually.of_forall fun t => mul_nonneg (by positivity) (_hM0 t))).symm

  have hmain : ∫⁻ x, ‖∫ t : ℝ, G (t, x)‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (Real.pi * ∫ t : ℝ, (1 + t ^ 2) * M t) := by
    calc ∫⁻ x, ‖∫ t : ℝ, G (t, x)‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal Real.pi * (∫⁻ t : ℝ, ENNReal.ofReal (1 + t ^ 2) * ‖G (t, x)‖ₑ ^ 2) ∂μ :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal Real.pi * (∫⁻ x, (∫⁻ t : ℝ, ENNReal.ofReal (1 + t ^ 2) * ‖G (t, x)‖ₑ ^ 2) ∂μ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Real.pi * ENNReal.ofReal (∫ t : ℝ, (1 + t ^ 2) * M t) := by
          gcongr
      _ = ENNReal.ofReal (Real.pi * ∫ t : ℝ, (1 + t ^ 2) * M t) := by
          rw [ENNReal.ofReal_mul Real.pi_pos.le]

  have hint2 : Integrable (fun x => ‖∫ t : ℝ, G (t, x)‖ ^ 2) μ := by
    refine ⟨(continuous_pow 2).comp_aestronglyMeasurable hmeas.norm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have e : ∀ x, ‖‖∫ t : ℝ, G (t, x)‖ ^ 2‖ₑ = ‖∫ t : ℝ, G (t, x)‖ₑ ^ 2 := fun x => by
      rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [e]
    exact hmain.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 hint2, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
    hint2.aestronglyMeasurable]
  have hI : 0 ≤ Real.pi * ∫ t : ℝ, (1 + t ^ 2) * M t :=
    mul_nonneg Real.pi_pos.le (integral_nonneg fun t => mul_nonneg (by positivity) (_hM0 t))
  have e2 : ∫⁻ x, ENNReal.ofReal (‖∫ t : ℝ, G (t, x)‖ ^ 2) ∂μ = ∫⁻ x, ‖∫ t : ℝ, G (t, x)‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [e2]
  calc (∫⁻ x, ‖∫ t : ℝ, G (t, x)‖ₑ ^ 2 ∂μ).toReal
      ≤ (ENNReal.ofReal (Real.pi * ∫ t : ℝ, (1 + t ^ 2) * M t)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = Real.pi * ∫ t : ℝ, (1 + t ^ 2) * M t := ENNReal.toReal_ofReal hI

end S_MeasureTheory_memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul
end P2MW
export P2MW.S_MeasureTheory_memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul (solution)
