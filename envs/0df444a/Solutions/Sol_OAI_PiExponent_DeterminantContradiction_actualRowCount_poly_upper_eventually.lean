-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_poly_upper_eventually
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:21:21.076714+00:00
-- url     : https://prove2.me/submissions/b19eaa05-660f-4457-912d-d0773711300a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_real_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
      (actualRowCount d H : ℝ) ≤ C * (H + 1) ^ (d.m + 1) := by
  let A : ℝ := max 1 (1 / (d.v0 : ℝ))
  have hA : 0 < A := by
    dsimp [A]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKpos : 0 < (d.K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one d.K_pos)
  refine ⟨(d.K : ℝ) * A, mul_pos hKpos hA, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  have hrow := OAI.PiExponent.DeterminantContradiction.actualRowCount_real_bound d H hH
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAi : 1 / (d.v0 : ℝ) ≤ A := le_max_right _ _
  have hAiInv : (d.v0 : ℝ)⁻¹ ≤ A := by simpa [one_div] using hAi
  have hfactor : H / (d.v0 : ℝ) + 1 ≤ A * (H + 1) := by
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg hH (sub_nonneg.mpr hAiInv), sub_nonneg.mpr hA1]
  have hpow : 0 ≤ (H + 1) ^ d.m := by positivity
  have hK : 0 ≤ (d.K : ℝ) := Nat.cast_nonneg _
  calc
    (actualRowCount d H : ℝ) ≤ (d.K : ℝ) * (H / (d.v0 : ℝ) + 1) * (H + 1) ^ d.m := hrow
    _ ≤ (d.K : ℝ) * (A * (H + 1)) * (H + 1) ^ d.m := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor hK) hpow
    _ = ((d.K : ℝ) * A) * (H + 1) ^ (d.m + 1) := by
      rw [pow_succ]
      ring