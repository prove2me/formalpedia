-- Prove2me | solution 1 for OAI.PiExponent.translation_term_count_log_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:43:41.107371+00:00
-- url     : https://prove2.me/submissions/f0346c06-7d6b-46a3-b979-b8820fc51e0b

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_floor_linear_log_div_tendsto_zero
import Theorems.Thm_OAI_PiExponent_translation_term_count_log_factorization

open scoped BigOperators Topology
open Filter
open OAI.PiExponent

theorem solution (m : ℕ) (v : ℝ) (hv : 0 < v) :
    Tendsto (fun H : ℝ => Real.log (translationTermCount m v H : ℝ) / H)
      atTop (𝓝 0) := by
  have hfirst : Tendsto
      (fun H : ℝ => Real.log ((⌊H / (1 : ℝ)⌋₊ + 1 : ℕ) : ℝ) / H)
      atTop (𝓝 0) := by
    simpa using
      (OAI.PiExponent.floor_linear_log_div_tendsto_zero (1 : ℝ) (by exact one_pos))
  have hsecond : Tendsto
      (fun H : ℝ => Real.log ((⌊H / v⌋₊ + 1 : ℕ) : ℝ) / H)
      atTop (𝓝 0) :=
    OAI.PiExponent.floor_linear_log_div_tendsto_zero v hv
  have hsum : Tendsto
      (fun H : ℝ => (2 * (m : ℝ)) *
        (Real.log ((⌊H / (1 : ℝ)⌋₊ + 1 : ℕ) : ℝ) / H) +
        Real.log ((⌊H / v⌋₊ + 1 : ℕ) : ℝ) / H)
      atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hfirst).add hsecond
  have hEq :
      (fun H : ℝ => Real.log (translationTermCount m v H : ℝ) / H) =
        (fun H : ℝ => (2 * (m : ℝ)) *
          (Real.log ((⌊H / (1 : ℝ)⌋₊ + 1 : ℕ) : ℝ) / H) +
          Real.log ((⌊H / v⌋₊ + 1 : ℕ) : ℝ) / H) := by
    funext H
    exact OAI.PiExponent.translation_term_count_log_factorization m v H
  rw [hEq]
  exact hsum