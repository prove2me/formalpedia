-- Prove2me | solution 1 for OAI.PiExponent.floor_linear_log_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:54:48.005184+00:00
-- url     : https://prove2.me/submissions/3f74c72d-e7aa-4b48-bf11-c3ef75171d1d

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Mathlib.Algebra.Order.Floor.Semiring

open scoped BigOperators Topology
open Filter
open OAI.PiExponent

theorem solution (c : ℝ) (hc : 0 < c) :
    Tendsto (fun H : ℝ => Real.log ((⌊H / c⌋₊ + 1 : ℕ) : ℝ) / H)
      atTop (𝓝 0) := by
  have harg : Tendsto (fun H : ℝ => H / c + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 (tendsto_id.atTop_div_const hc)
  have hupper : Tendsto (fun H : ℝ => Real.log (H / c + 1) / H) atTop (𝓝 0) := by
    have heq : (fun H : ℝ => Real.log (H / c + 1) / H) =
        (fun H : ℝ => Real.log (H / c + 1) ^ 1 / (c * (H / c + 1) + -c)) := by
      funext H
      rw [pow_one]
      congr 1
      field_simp [hc.ne']
      <;> ring
    rw [heq]
    exact (Real.tendsto_pow_log_div_mul_add_atTop c (-c) 1 hc.ne').comp harg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    have hfloor : ((⌊H / c⌋₊ : ℕ) : ℝ) ≤ H / c :=
      Nat.floor_le (div_nonneg hH.le hc.le)
    have harg_le : ((⌊H / c⌋₊ + 1 : ℕ) : ℝ) ≤ H / c + 1 := by
      norm_num [Nat.cast_add]
      linarith [hfloor]
    have hnat : 1 ≤ (⌊H / c⌋₊ + 1 : ℕ) := Nat.le_add_left 1 _
    have hcast : (1 : ℝ) ≤ ((⌊H / c⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hnum : 0 ≤ Real.log ((⌊H / c⌋₊ + 1 : ℕ) : ℝ) := Real.log_nonneg hcast
    exact div_nonneg hnum hH.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    have hfloor : ((⌊H / c⌋₊ : ℕ) : ℝ) ≤ H / c :=
      Nat.floor_le (div_nonneg hH.le hc.le)
    have harg_le : ((⌊H / c⌋₊ + 1 : ℕ) : ℝ) ≤ H / c + 1 := by
      norm_num [Nat.cast_add]
      linarith [hfloor]
    have hlog : Real.log ((⌊H / c⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (H / c + 1) :=
      Real.log_le_log (by positivity) harg_le
    exact div_le_div_of_nonneg_right hlog hH.le