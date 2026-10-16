-- Prove2me | solution 1 for OAI.RandomKSAT.killRatio_le_density_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:42:24.299982+00:00
-- url     : https://prove2.me/submissions/1b10b389-6278-4231-9af4-13dc68af199a

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FrozenReplacement.lean:L40-L59
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.killRatio_le_density_pow. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance

-- ---- from OAI.Probability.SATVariance.FrozenReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma killRatio_zero (u b : ℕ) : killRatio u b 0 = 1 := by
  simp [killRatio]

lemma killRatio_eq_zero {u b s : ℕ} (hbs : b < s) : killRatio u b s = 0 := by
  simp [killRatio, Nat.choose_eq_zero_of_lt hbs]

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

lemma killRatio_le_density_pow {u b s : ℕ} (hbu : b ≤ u) (hsu : s ≤ u) :
    killRatio u b s ≤ ((b : ℝ) / (2 * u)) ^ s := by
  induction s with
  | zero => simp [killRatio_zero]
  | succ s ih =>
    by_cases hbs : b < s+1
    · rw [killRatio_eq_zero hbs]
      positivity
    · have hsb : s ≤ b := by omega
      have hsu' : s < u := by omega
      have hus : (0 : ℝ) < (u : ℝ) - s := sub_pos.mpr (by exact_mod_cast hsu')
      have hu : (0 : ℝ) < u := by exact_mod_cast (Nat.zero_le s).trans_lt hsu'
      have hbu' : (b : ℝ) ≤ u := by exact_mod_cast hbu
      have hs : (0 : ℝ) ≤ s := by positivity
      have hfactor : ((b : ℝ)-s) / (2 * (u-s)) ≤ (b : ℝ)/(2*u) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      rw [killRatio_succ hsu' hsb, mul_div_assoc, pow_succ]
      have hbs₀ : (0 : ℝ) ≤ (b : ℝ) - s := sub_nonneg.mpr (by exact_mod_cast hsb)
      exact mul_le_mul (ih (by omega)) hfactor (by positivity) (by positivity)

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.killRatio_le_density_pow := @_root_.OAI.RandomKSAT.killRatio_le_density_pow
