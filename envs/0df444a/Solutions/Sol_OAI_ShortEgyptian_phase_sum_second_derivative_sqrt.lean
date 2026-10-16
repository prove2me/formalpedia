-- Prove2me | solution 1 for OAI.ShortEgyptian.phase_sum_second_derivative_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:17:12.561861+00:00
-- url     : https://prove2.me/submissions/9aa56747-43ca-4b88-968c-bd22c427ba2a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/IntervalDifferencing.lean:L20-L41
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.phase_sum_second_derivative_sqrt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Theorems.Thm_OAI_ShortEgyptian_phase_sum_second_derivative

-- ---- from OAI.NumberTheory.ShortEgyptian.IntervalDifferencing ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uκ uM

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem phase_sum_second_derivative_sqrt (f : ℕ → ℝ) (N : ℕ) {lam A : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hstep : ∀ n < N,
      lam ≤ (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ∧
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ≤ A * lam) :
    ‖∑ n ∈ range (N + 1), phase (f n)‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 6 := by
  have hs := phase_sum_second_derivative f N hlam (Real.sqrt_pos.mpr hlam) hstep
  have hsq := Real.sq_sqrt hlam.le
  have hsp := Real.sqrt_pos.mpr hlam
  have hlams : lam ≤ Real.sqrt lam := (Real.le_sqrt hlam.le hlam.le).mpr (by nlinarith)
  have heq : (A * lam * N + 2) * (2 * Real.sqrt lam / lam + 1 / Real.sqrt lam + 3) =
      3 * A * N * Real.sqrt lam + 3 * A * N * lam + 6 / Real.sqrt lam + 6 := by
    have hdiv : 2 * Real.sqrt lam / lam = 2 / Real.sqrt lam := by
      apply (div_eq_div_iff hlam.ne' hsp.ne').mpr
      nlinarith [hsq]
    rw [hdiv]
    field_simp
    nlinarith [congrArg (fun z : ℝ => 3 * A * (N : ℝ) * z) hsq]
  rw [heq] at hs
  have hh := mul_le_mul_of_nonneg_left hlams (show 0 ≤ 3 * A * (N : ℝ) by positivity)
  linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.phase_sum_second_derivative_sqrt := @_root_.OAI.ShortEgyptian.phase_sum_second_derivative_sqrt
