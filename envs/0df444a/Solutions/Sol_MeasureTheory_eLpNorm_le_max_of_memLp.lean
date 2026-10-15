-- Prove2me | solution 1 for MeasureTheory.eLpNorm_le_max_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T20:46:32.727329+00:00
-- url     : https://prove2.me/submissions/9c861ae9-0160-4d3b-8e0c-b37fd851dfc4

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MeasureTheory

theorem solution {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {p q r : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hqr : q ≤ r)
    {f : α → E} (hfp : MemLp f (ENNReal.ofReal p) μ)
    (hfr : MemLp f (ENNReal.ofReal r) μ) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      max (eLpNorm f (ENNReal.ofReal p) μ) (eLpNorm f (ENNReal.ofReal r) μ) := by
  have hq : 0 < q := hp.trans_le hpq
  have hr : 0 < r := hq.trans_le hqr
  rcases eq_or_lt_of_le (hpq.trans hqr) with hpr | hpr
  · have hpq' : p = q := le_antisymm hpq (hpr ▸ hqr)
    subst q
    exact le_max_left _ _
  let t : ℝ := (r - q) / (r - p)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hqr) (sub_pos.mpr hpr).le
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hpr)).mpr (by linarith)
  have hs : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hweights : p * t + r * (1 - t) = q := by
    dsimp [t]
    field_simp
    <;> ring
  let M := max (eLpNorm f (ENNReal.ofReal p) μ) (eLpNorm f (ENNReal.ofReal r) μ)
  have hnorm (s : ℝ) (hs : 0 < s) :
      eLpNorm f (ENNReal.ofReal s) μ = eLpNorm' f s μ := by
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hs.le]
  have hIp : (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ≤ M ^ p := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hp, ← hnorm p hp]
    exact ENNReal.rpow_le_rpow (le_max_left _ _) hp.le
  have hIr : (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ≤ M ^ r := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hr, ← hnorm r hr]
    exact ENNReal.rpow_le_rpow (le_max_right _ _) hr.le
  rw [hnorm q hq, eLpNorm', one_div, ENNReal.rpow_inv_le_iff hq]
  calc
    (∫⁻ x, ‖f x‖ₑ ^ q ∂μ) =
        ∫⁻ x, (‖f x‖ₑ ^ p) ^ t * (‖f x‖ₑ ^ r) ^ (1 - t) ∂μ := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hp.le ht) (mul_nonneg hr.le hs),
        hweights]
    _ ≤ (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ t * (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (1 - t) :=
      ENNReal.lintegral_mul_norm_pow_le
        (hfp.aestronglyMeasurable.enorm.pow_const p)
        (hfr.aestronglyMeasurable.enorm.pow_const r) ht hs (by ring)
    _ ≤ (M ^ p) ^ t * (M ^ r) ^ (1 - t) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hIp ht) (ENNReal.rpow_le_rpow hIr hs)
    _ = M ^ q := by
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hp.le ht) (mul_nonneg hr.le hs),
        hweights]
