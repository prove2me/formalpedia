-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.exp_small_lt_half_cube
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:38:45.555253+00:00
-- url     : https://prove2.me/submissions/3523002e-9aee-49dc-9408-60b238047fb2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L407-L424
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.exp_small_lt_half_cube. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- The Boolean cube is larger than the entropy bounds used above. -/
theorem exp_small_lt_half_cube {n : ℕ} (hn : 32 ≤ n) :
    Real.exp (13 * n / 32) < (2 : ℝ) ^ n / 2 := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hu : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hn' : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : 13 * (n : ℝ) / 32 < n * Real.log 2 - Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  calc
    _ < Real.exp (n * Real.log 2 - Real.log 2) := Real.exp_lt_exp.mpr hlt
    _ = _ := by rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num)]

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.exp_small_lt_half_cube := @_root_.OAI.AsymptoticallyMinimalLittlewood.exp_small_lt_half_cube
