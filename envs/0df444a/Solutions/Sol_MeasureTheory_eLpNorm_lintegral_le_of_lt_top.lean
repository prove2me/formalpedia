-- Prove2me | solution 1 for MeasureTheory.eLpNorm_lintegral_le_of_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T18:25:21.356274+00:00
-- url     : https://prove2.me/submissions/1e4d48fc-52a0-454e-b81b-127598801b95

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MeasureTheory MeasureTheory.Measure

theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {q : ℝ} (hq : 1 < q) (G : α → β → ENNReal)
    (hG : AEMeasurable (Function.uncurry G) (μ.prod ν))
    (hbound : (∫⁻ y, eLpNorm (fun x => G x y) (ENNReal.ofReal q) μ ∂ν) < ⊤) :
    eLpNorm (fun x => ∫⁻ y, G x y ∂ν) (ENNReal.ofReal q) μ ≤
      ∫⁻ y, eLpNorm (fun x => G x y) (ENNReal.ofReal q) μ ∂ν := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have norm_formula (f : α → ENNReal) :
      eLpNorm f (ENNReal.ofReal q) μ = (∫⁻ x, f x ^ q ∂μ) ^ (1 / q) := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le, enorm_eq_self, one_div]
  suffices core : ∀ K : α → β → ENNReal,
      Measurable (Function.uncurry K) →
      (∫⁻ y, (∫⁻ x, K x y ^ q ∂μ) ^ (1 / q) ∂ν) < ⊤ →
      (∫⁻ x, (∫⁻ y, K x y ∂ν) ^ q ∂μ) ^ (1 / q) ≤
        ∫⁻ y, (∫⁻ x, K x y ^ q ∂μ) ^ (1 / q) ∂ν by
    let K : α → β → ENNReal := fun x y => hG.mk (Function.uncurry G) (x, y)
    have heq : Function.uncurry G =ᵐ[μ.prod ν] Function.uncurry K := hG.ae_eq_mk
    have heqx := ae_ae_of_ae_prod heq
    have heqy := ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp heq)
    have hrhs : (∫⁻ y, eLpNorm (fun x => G x y) (ENNReal.ofReal q) μ ∂ν) =
        ∫⁻ y, (∫⁻ x, K x y ^ q ∂μ) ^ (1 / q) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [heqy] with y hy
      change (fun x => G x y) =ᵐ[μ] (fun x => K x y) at hy
      rw [eLpNorm_congr_ae hy, norm_formula]
    have hlhs : eLpNorm (fun x => ∫⁻ y, G x y ∂ν) (ENNReal.ofReal q) μ =
        (∫⁻ x, (∫⁻ y, K x y ∂ν) ^ q ∂μ) ^ (1 / q) := by
      have hi : (fun x => ∫⁻ y, G x y ∂ν) =ᵐ[μ] (fun x => ∫⁻ y, K x y ∂ν) :=
        heqx.mono fun x hx => lintegral_congr_ae hx
      rw [eLpNorm_congr_ae hi, norm_formula]
    rw [hlhs, hrhs]
    exact core K hG.measurable_mk (hrhs ▸ hbound)
  intro K hK hb
  let a : β → ENNReal := fun y => (∫⁻ x, K x y ^ q ∂μ) ^ (1 / q)
  let B : ENNReal := ∫⁻ y, a y ∂ν
  let W : α → β → ENNReal := fun x y => K x y ^ q * a y ^ (1 - q)
  have ha : Measurable a := (hK.pow_const q).lintegral_prod_left.pow_const _
  have hW : Measurable (Function.uncurry W) :=
    (hK.pow_const q).mul ((ha.comp measurable_snd).pow_const _)
  have hapow (y : β) : a y ^ q = ∫⁻ x, K x y ^ q ∂μ := by
    dsimp [a]
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have hatop : ∀ᵐ y ∂ν, a y ≠ ⊤ :=
    (ae_lt_top ha hb.ne).mono fun y hy => hy.ne
  have hsection : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ,
      W x y ^ (1 / q) * a y ^ (1 - 1 / q) = K x y := by
    filter_upwards [hatop] with y hytop
    by_cases hy0 : a y = 0
    · have hz : ∫⁻ x, K x y ^ q ∂μ = 0 := by rw [← hapow, hy0]; simp [hq0]
      have hzAE := ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero hq0.le
        (hK.of_uncurry_right.aemeasurable) hz
      filter_upwards [hzAE] with x hx
      simp [W, hx, hq0]
    · filter_upwards [] with x
      dsimp [W]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      have hqq : q * (1 / q) = 1 := by field_simp
      have hexp : (1 - q) * (1 / q) + (1 - 1 / q) = 0 := by field_simp; ring
      rw [hqq, ENNReal.rpow_one, mul_assoc,
        ← ENNReal.rpow_add _ _ hy0 hytop, hexp, ENNReal.rpow_zero, mul_one]
  have hsection' : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν,
      W x y ^ (1 / q) * a y ^ (1 - 1 / q) = K x y := by
    apply (ae_ae_comm (μ := μ) (ν := ν)
      (p := fun x y => W x y ^ (1 / q) * a y ^ (1 - 1 / q) = K x y) ?_).mpr hsection
    exact measurableSet_eq_fun
      ((hW.pow_const _).mul ((ha.comp measurable_snd).pow_const _)) hK
  have hWint : (∫⁻ x, ∫⁻ y, W x y ∂ν ∂μ) = B := by
    rw [lintegral_lintegral_swap hW.aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [hatop] with y hytop
    by_cases hy0 : a y = 0
    · have hz : ∫⁻ x, K x y ^ q ∂μ = 0 := by rw [← hapow, hy0]; simp [hq0]
      have hzAE := ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero hq0.le
        (hK.of_uncurry_right.aemeasurable) hz
      calc
        (∫⁻ x, W x y ∂μ) = ∫⁻ x, (0 : ENNReal) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hzAE] with x hx
          simp [W, hx, hq0]
        _ = a y := by simp [hy0]
    · dsimp [W]
      rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_ne_zero hy0 hytop)]
      rw [← hapow, ← ENNReal.rpow_add _ _ hy0 hytop]
      simp
  have ht : 0 ≤ 1 / q := by positivity
  have hu : 0 ≤ 1 - 1 / q := by
    have : 1 / q < 1 := (div_lt_one hq0).mpr hq
    linarith
  have hpoint : ∀ᵐ x ∂μ, (∫⁻ y, K x y ∂ν) ^ q ≤
      (∫⁻ y, W x y ∂ν) * B ^ (q - 1) := by
    filter_upwards [hsection'] with x hx
    have hholder := ENNReal.lintegral_mul_norm_pow_le (μ := ν) (f := W x) (g := a)
      (hW.of_uncurry_left.aemeasurable) ha.aemeasurable ht hu (by ring)
    have heq : (∫⁻ y, W x y ^ (1 / q) * a y ^ (1 - 1 / q) ∂ν) =
        ∫⁻ y, K x y ∂ν := lintegral_congr_ae hx
    rw [heq] at hholder
    have hr := ENNReal.rpow_le_rpow hholder hq0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hr
    have htq : (1 / q) * q = 1 := by field_simp
    have huq : (1 - 1 / q) * q = q - 1 := by field_simp
    simpa only [htq, huq, ENNReal.rpow_one] using hr
  have hint : (∫⁻ x, (∫⁻ y, K x y ∂ν) ^ q ∂μ) ≤ B ^ q := by
    calc
      _ ≤ ∫⁻ x, (∫⁻ y, W x y ∂ν) * B ^ (q - 1) ∂μ := lintegral_mono_ae hpoint
      _ = B * B ^ (q - 1) := by
        rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hb.ne),
          hWint]
      _ = B ^ q := by
        calc
          B * B ^ (q - 1) = B ^ (1 : ℝ) * B ^ (q - 1) := by rw [ENNReal.rpow_one]
          _ = B ^ (1 + (q - 1)) :=
            (ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith)).symm
          _ = B ^ q := by congr 1; ring
  have hr := ENNReal.rpow_le_rpow hint ht
  rw [← ENNReal.rpow_mul] at hr
  have hqq : q * (1 / q) = 1 := by field_simp
  simpa only [hqq, ENNReal.rpow_one] using hr
