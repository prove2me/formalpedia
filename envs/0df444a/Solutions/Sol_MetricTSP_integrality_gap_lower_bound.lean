-- Prove2me | solution 1 for MetricTSP.integrality_gap_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T20:14:24.479889+00:00
-- url     : https://prove2.me/submissions/dc580666-dd34-47d1-9b3f-ca4f413af01b

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths
import Theorems.Thm_MetricTSP_three_paths_metric
import Theorems.Thm_MetricTSP_three_paths_cert_feasible
import Theorems.Thm_MetricTSP_three_paths_cert_objective
import Theorems.Thm_MetricTSP_three_paths_opt_lower
import Theorems.Thm_MetricTSP_three_paths_separated
import Theorems.Thm_MetricTSP_hk_value_ge_card
import Theorems.Thm_MetricTSP_hk_value_le_of_feasible

namespace MetricTSP

/-- **The 4/3 lower bound.** For every `ε > 0` the three-parallel-paths instance with
`k ≈ 1/ε` has integrality gap at least `4/3 - ε`. -/
theorem gap_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → Fin n → ℝ), 3 ≤ n ∧ IsMetricCost c ∧
      0 < hkValue c ∧ (4 / 3 - ε) * hkValue c ≤ tspOpt c := by
  set k : ℕ := max 2 ⌈2 / ε⌉₊ with hkdef
  have hk2 : 2 ≤ k := le_max_left _ _
  have hkceil : (2 / ε : ℝ) ≤ k := by
    calc (2 / ε : ℝ) ≤ ⌈2 / ε⌉₊ := Nat.le_ceil _
      _ ≤ k := by exact_mod_cast le_max_right _ _
  refine ⟨3*k+2, tpCost k, by omega, three_paths_metric k (by omega), ?_, ?_⟩
  · have h1 := hk_value_ge_card (3*k+2) (by omega) (tpCost k)
      (three_paths_separated k (by omega))
    have h2 : (0:ℝ) < ((3*k+2 : ℕ) : ℝ) := by
      push_cast
      positivity
    linarith
  · have hub : hkValue (tpCost k) ≤ 3*k+3 := by
      have hle := hk_value_le_of_feasible (3*k+2) (tpCost k)
        (three_paths_metric k (by omega)) (tpCert k) (three_paths_cert_feasible k hk2)
      have hobj := three_paths_cert_objective k hk2
      linarith
    have hlb := three_paths_opt_lower k hk2
    have hpos : (0:ℝ) < hkValue (tpCost k) := by
      have h1 := hk_value_ge_card (3*k+2) (by omega) (tpCost k)
        (three_paths_separated k (by omega))
      have h2 : (0:ℝ) < ((3*k+2 : ℕ) : ℝ) := by
        push_cast
        positivity
      linarith
    have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
    by_cases hbig : 4/3 - ε ≤ 0
    · have h1 : (4/3 - ε) * hkValue (tpCost k) ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨hbig, le_of_lt hpos⟩)
      linarith
    · push_neg at hbig
      have hεk : (2:ℝ) ≤ ε * k := by
        have h1 : ε * (2/ε) ≤ ε * k := mul_le_mul_of_nonneg_left hkceil (le_of_lt hε)
        have h2 : ε * (2/ε) = 2 := by field_simp
        linarith
      have hchain : (4/3 - ε) * hkValue (tpCost k) ≤ (4/3 - ε) * (3*(k:ℝ)+3) :=
        mul_le_mul_of_nonneg_left hub (le_of_lt hbig)
      have harith : (4/3 - ε) * (3*(k:ℝ)+3) ≤ 4*(k:ℝ)+2 := by nlinarith
      linarith

end MetricTSP

open MetricTSP

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → Fin n → ℝ), 3 ≤ n ∧ IsMetricCost c ∧
      0 < hkValue c ∧ (4 / 3 - ε) * hkValue c ≤ tspOpt c :=
  MetricTSP.gap_lower ε hε
