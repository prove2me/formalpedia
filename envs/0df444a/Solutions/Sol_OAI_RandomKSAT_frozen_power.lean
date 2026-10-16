-- Prove2me | solution 1 for OAI.RandomKSAT.frozen_power
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:44:29.794549+00:00
-- url     : https://prove2.me/submissions/353ee434-28fd-43e8-a4c3-3c057992f6f2

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FrozenReplacement.lean:L85-L102
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.frozen_power. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Theorems.Thm_OAI_RandomKSAT_killRatio_le_density_pow

-- ---- from OAI.Probability.SATVariance.FrozenReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma killRatio_nonneg (u b s : ℕ) : 0 ≤ killRatio u b s := by
  unfold killRatio
  positivity

lemma killRatio_succ {u b s : ℕ} (hsu : s < u) (hsb : s ≤ b) :
    killRatio u b (s + 1) = killRatio u b s * ((b : ℝ) - s) / (2 * (u - s)) := by
  have hu : (0 : ℝ) < u.choose s := by exact_mod_cast Nat.choose_pos hsu.le
  have hu' : (0 : ℝ) < u.choose (s+1) := by exact_mod_cast Nat.choose_pos hsu
  have hus : (0 : ℝ) < (u : ℝ) - s := sub_pos.mpr (by exact_mod_cast hsu)
  have hb := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq b s)
  have hn := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq u s)
  push_cast [Nat.cast_sub hsb] at hb
  push_cast [Nat.cast_sub hsu.le] at hn
  unfold killRatio
  rw [pow_succ]
  apply (div_eq_iff (by positivity : (2 : ℝ)^s * 2 * u.choose (s+1) ≠ 0)).2
  field_simp
  nlinarith [mul_pos hu hus]

lemma killRatio_root_le {u b r : ℕ} (hr : 0 < r) (hbu : b ≤ u) (hru : r ≤ u) :
    (killRatio u b r) ^ ((r : ℝ)⁻¹) ≤ (b : ℝ) / (2*u) := by
  have hr₀ : (r : ℝ) ≠ 0 := by positivity
  have h := Real.rpow_le_rpow (killRatio_nonneg u b r)
    (killRatio_le_density_pow hbu hru) (by positivity : (0 : ℝ) ≤ (r : ℝ)⁻¹)
  rw [← Real.rpow_natCast_mul (by positivity), mul_inv_cancel₀ hr₀,
    Real.rpow_one] at h
  exact h

lemma frozen_power {u b r : ℕ} (hr : 1 ≤ r) (hbu : b ≤ u) (hrb : r+1 ≤ b) :
    (killRatio u b r) ^ (((r : ℝ)+1)/r) / (r+1) ≤ killRatio u b (r+1) := by
  have hru : r < u := by omega
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast hr
  have hu₀ : (0 : ℝ) < u := by exact_mod_cast (Nat.zero_le r).trans_lt hru
  have hus : (0 : ℝ) < (u : ℝ)-r := sub_pos.mpr (by exact_mod_cast hru)
  have hrb' : (r : ℝ)+1 ≤ b := by exact_mod_cast hrb
  have hbu' : (b : ℝ) ≤ u := by exact_mod_cast hbu
  have hstep : (b : ℝ)/(2*u)/(r+1) ≤ ((b : ℝ)-r)/(2*(u-r)) := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hrb') (le_of_lt hr₀)]
  have he : ((r : ℝ)+1)/r = 1+(r : ℝ)⁻¹ := by field_simp
  rw [he, Real.rpow_add_of_nonneg (killRatio_nonneg u b r) zero_le_one (by positivity),
    Real.rpow_one, mul_div_assoc, killRatio_succ hru (by omega), mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (killRatio_nonneg u b r)
  exact (div_le_div_of_nonneg_right (killRatio_root_le (by omega) hbu hru.le)
    (by positivity)).trans hstep

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.frozen_power := @_root_.OAI.RandomKSAT.frozen_power
