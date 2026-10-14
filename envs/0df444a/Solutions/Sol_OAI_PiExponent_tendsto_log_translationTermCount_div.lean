-- Prove2me | solution 1 for OAI.PiExponent.tendsto_log_translationTermCount_div
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T21:41:36.533684+00:00
-- url     : https://prove2.me/submissions/6dc9adc6-6fee-40c8-9d58-9d9e74e6b54a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_tendsto_log_div_of_normalized_pow

namespace OAI

open Filter Topology

namespace PiExponent

private theorem tendsto_natFloor_affine_div {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => (⌊a * x + b⌋₊ : ℝ) / x) atTop (𝓝 a) := by
  have hy : Tendsto (fun x : ℝ => a * x + b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id)
  have hratio : Tendsto (fun x : ℝ => (a * x + b) / x) atTop (𝓝 a) := by
    have h : Tendsto (fun x : ℝ => a + b * x⁻¹) atTop (𝓝 (a + b * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)))
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have h := (tendsto_nat_floor_div_atTop.comp hy).mul hratio
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hy.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  change (⌊a * x + b⌋₊ : ℝ) / (a * x + b) * ((a * x + b) / x) = _
  field_simp

private theorem tendsto_natFloor_mul_add_one_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H : ℝ => ((⌊a * H⌋₊ + 1 : ℕ) : ℝ) / H) atTop (𝓝 a) := by
  have h := (tendsto_natFloor_affine_div ha 0).add (tendsto_id.const_div_atTop (1 : ℝ))
  simpa only [add_zero, id_eq, Nat.cast_add, Nat.cast_one, add_div] using h

private theorem tendsto_translationTermCount_normalized (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => (translationTermCount m v H : ℝ) / H ^ (2 * m + 1))
      atTop (𝓝 (1 / v)) := by
  have h₁ : Tendsto (fun H : ℝ => ((⌊H⌋₊ + 1 : ℕ) : ℝ) / H) atTop (𝓝 1) := by
    simpa only [one_mul] using tendsto_natFloor_mul_add_one_div (show (0 : ℝ) < 1 by norm_num)
  have h₂ : Tendsto (fun H : ℝ => ((⌊H / v⌋₊ + 1 : ℕ) : ℝ) / H)
      atTop (𝓝 (1 / v)) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using
      tendsto_natFloor_mul_add_one_div (div_pos zero_lt_one hv)
  have h := (h₁.pow (2 * m)).mul h₂
  simp only [one_pow, one_mul] at h
  convert h using 1
  ext H
  simp only [translationTermCount, Nat.cast_mul, Nat.cast_pow, div_pow, div_mul_div_comm,
    pow_succ]
end PiExponent

end OAI

open Filter Topology
open OAI.PiExponent

theorem solution (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => Real.log (translationTermCount m v H : ℝ) / H)
      atTop (𝓝 0) :=
  tendsto_log_div_of_normalized_pow (tendsto_translationTermCount_normalized m hv)
    (div_pos zero_lt_one hv)
