-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.tendsto_translationLogTerm
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T16:12:07.370975+00:00
-- url     : https://prove2.me/submissions/329bab12-579a-4bf7-81dd-293436acd51f

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    Tendsto (fun H : ℝ => Real.log (translationTermCount d.m d.v0 H : ℝ) / H) atTop (𝓝 0) := by
  let C : ℝ := 2 ^ (2 * d.m) * (1 / (d.v0 : ℝ) + 1)
  have hC : 0 < C := by
    dsimp [C]
    have hv : 0 < (d.v0 : ℝ) := d.v0_pos
    positivity
  have hlogquot : Tendsto (fun H : ℝ => Real.log H / H) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hconst : Tendsto (fun H : ℝ => Real.log C / H) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := Real.log C)).mul tendsto_inv_atTop_zero
  have hn : Tendsto (fun H : ℝ => (2 * d.m + 1 : ℕ) * (Real.log H / H)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 * d.m + 1 : ℝ))).mul hlogquot
  have hupper : Tendsto (fun H : ℝ => Real.log C / H + (2 * d.m + 1 : ℕ) * (Real.log H / H)) atTop (𝓝 0) := by
    simpa using hconst.add hn
  refine tendsto_const_nhds.squeeze' hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with H hH
    have hfloor : 1 ≤ translationTermCount d.m d.v0 H := by
      unfold translationTermCount
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hfloor)) (by linarith)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with H hH
    have hHpos : 0 < H := by linarith
    have hv : 0 < (d.v0 : ℝ) := d.v0_pos
    have hfirst : (⌊H⌋₊ : ℝ) + 1 ≤ 2 * H := by
      calc
        (⌊H⌋₊ : ℝ) + 1 ≤ H + 1 := by exact add_le_add (Nat.floor_le (le_of_lt hHpos)) le_rfl
        _ ≤ 2 * H := by linarith
    have hsecond : (⌊H / (d.v0 : ℝ)⌋₊ : ℝ) + 1 ≤ (1 / (d.v0 : ℝ) + 1) * H := by
      calc
        (⌊H / (d.v0 : ℝ)⌋₊ : ℝ) + 1 ≤ H / (d.v0 : ℝ) + 1 := by exact add_le_add (Nat.floor_le (by positivity)) le_rfl
        _ ≤ H / (d.v0 : ℝ) + H := add_le_add le_rfl hH
        _ = (1 / (d.v0 : ℝ) + 1) * H := by field_simp
    have hcount : (translationTermCount d.m d.v0 H : ℝ) ≤ C * H ^ (2 * d.m + 1 : ℕ) := by
      unfold translationTermCount
      push_cast
      calc
        ((⌊H⌋₊ : ℝ) + 1) ^ (2 * d.m) * ((⌊H / (d.v0 : ℝ)⌋₊ : ℝ) + 1) ≤
            (2 * H) ^ (2 * d.m) * ((1 / (d.v0 : ℝ) + 1) * H) := by
              gcongr
        _ = C * H ^ (2 * d.m + 1 : ℕ) := by
              dsimp [C]
              rw [mul_pow, pow_succ]
              ring
    have hcountpos : 0 < (translationTermCount d.m d.v0 H : ℝ) := by
      have ht : 1 ≤ translationTermCount d.m d.v0 H := by
        unfold translationTermCount
        apply Nat.one_le_iff_ne_zero.mpr
        apply Nat.mul_ne_zero
        · exact pow_ne_zero _ (by omega)
        · omega
      exact_mod_cast ht
    have hlog : Real.log (translationTermCount d.m d.v0 H : ℝ) ≤
        Real.log C + (2 * d.m + 1 : ℕ) * Real.log H := by
      calc
        Real.log (translationTermCount d.m d.v0 H : ℝ) ≤ Real.log (C * H ^ (2 * d.m + 1 : ℕ)) :=
          Real.log_le_log hcountpos hcount
        _ = Real.log C + (2 * d.m + 1 : ℕ) * Real.log H := by
          rw [Real.log_mul hC.ne' (ne_of_gt (pow_pos hHpos _)), Real.log_pow]
    have hdiv := div_le_div_of_nonneg_right hlog (le_of_lt hHpos)
    convert hdiv using 1 <;> field_simp <;> ring
