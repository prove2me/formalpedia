-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.entropy_log_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:37:13.158836+00:00
-- url     : https://prove2.me/submissions/aadc3c5f-42ce-427c-ac6e-1b67389f3511

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L344-L405
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.entropy_log_parameters. The node keeps its source
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

/-- Numerical entropy estimates, with fixed generous absolute constants. -/
theorem entropy_log_parameters {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) :
    let L := Real.log (16 * R / s)
    1 / 2 ≤ L ∧ Real.exp (-4 * L) ≤ 1 / 2 ∧
      2 * R * Real.exp (-128 * L) ≤ s / (512 * L) ∧
      4 * R * Real.exp (-4 * L) ≤ s / 64 := by
  dsimp only
  let L := Real.log (16 * R / s)
  change 1 / 2 ≤ L ∧ _
  have hR : 0 < R := hs.trans_le hsR
  have hratio : (16 : ℝ) ≤ 16 * R / s := (le_div_iff₀ hs).mpr (by nlinarith)
  have hratio0 : 0 < 16 * R / s := by positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hL : (1 / 2 : ℝ) ≤ L := hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hL0 : 0 < L := by linarith
  have heq : Real.exp (-L) = s / (16 * R) := by
    dsimp [L]
    rw [Real.exp_neg, Real.exp_log hratio0, inv_div]
  have he : Real.exp (-L) ≤ 1 / 16 := by
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 16 * R)).mpr
    nlinarith
  have hbase : R * Real.exp (-L) = s / 16 := by
    rw [heq]
    field_simp

  have hfour : Real.exp (-4 * L) = Real.exp (-L) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdecay : Real.exp (-4 * L) ≤ 1 / 2 := by
    rw [hfour]
    calc
      _ ≤ (1 / 16 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le he 4
      _ ≤ _ := by norm_num
  have hpart : 4 * R * Real.exp (-4 * L) ≤ s / 64 := by
    have hp : Real.exp (-L) ^ 3 ≤ 1 / 16 := by
      calc
        _ ≤ (1 / 16 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
        _ ≤ _ := by norm_num
    calc
      _ = 4 * (R * Real.exp (-L)) * Real.exp (-L) ^ 3 := by rw [hfour]; ring
      _ = s / 4 * Real.exp (-L) ^ 3 := by rw [hbase]; ring
      _ ≤ s / 4 * (1 / 16) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hexp : 64 * L ≤ Real.exp (127 * L) := by
    nlinarith [Real.add_one_le_exp (127 * L)]
  have hmul : Real.exp (-128 * L) * (64 * L) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp (-128 * L) * Real.exp (127 * L) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmean : 2 * R * Real.exp (-128 * L) ≤ s / (512 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 512 * L)).mpr
    calc
      _ = 16 * R * (Real.exp (-128 * L) * (64 * L)) := by ring
      _ ≤ 16 * R * Real.exp (-L) := mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = s := by nlinarith [hbase]
  exact ⟨hL, hdecay, hmean, hpart⟩

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.entropy_log_parameters := @_root_.OAI.AsymptoticallyMinimalLittlewood.entropy_log_parameters
