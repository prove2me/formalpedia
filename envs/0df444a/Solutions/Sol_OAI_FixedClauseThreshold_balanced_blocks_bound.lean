-- Prove2me | solution 1 for OAI.FixedClauseThreshold.balanced_blocks_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:57:51.844999+00:00
-- url     : https://prove2.me/submissions/e67c3904-bf40-4357-b9fd-d38dc382b0ef

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Convergence.lean:L41-L121
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.balanced_blocks_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer
import Definitions.Def_OAI_Probability_RandomSAT_CenterComparison
import Definitions.Def_OAI_Probability_RandomSAT_Convergence

-- ---- from OAI.Probability.RandomSAT.Convergence ----
namespace OAI

/-!
A balanced-block geometric potential proves convergence from boundedness and
summable-min comparisons, including block counts that are not powers of two.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem balanceConstant_pos {β : ℝ} (hβ : 0 < β) : 0 < balanceConstant β :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hβ))

theorem balanced_power_potential {β a b q : ℝ} (hβ : 0 < β) (hb : 0 < b)
    (hq : 0 < q) (haq : q / 3 ≤ a) (hbq : b ≤ q / (3 / 2)) :
    a^(-β) ≤ balanceConstant β * (b^(-β) - q^(-β)) := by
  have hA := Real.rpow_le_rpow_of_nonpos (div_pos hq (by norm_num)) haq (neg_nonpos.mpr hβ.le)
  rw [Real.div_rpow hq.le (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    div_inv_eq_mul] at hA
  have hB := Real.rpow_le_rpow_of_nonpos hb hbq (neg_nonpos.mpr hβ.le)
  rw [Real.div_rpow hq.le (by norm_num : (0 : ℝ) ≤ 3 / 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 2), div_inv_eq_mul] at hB
  have hd : (3 / 2 : ℝ)^β - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hβ))
  have hf : balanceConstant β * ((3 / 2 : ℝ)^β - 1) = (3 : ℝ)^β := by
    exact div_mul_cancel₀ _ hd
  calc
    a^(-β) ≤ q^(-β) * (3 : ℝ)^β := hA
    _ = balanceConstant β * (q^(-β) * ((3 / 2 : ℝ)^β - 1)) := by rw [← hf]; ring
    _ ≤ balanceConstant β * (b^(-β) - q^(-β)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hB]) (balanceConstant_pos hβ).le

theorem balanced_blocks_bound (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    {N s : ℕ} (hsN : N ≤ s) (hs : 0 < s)
    (hadd : ∀ r ≥ N, ∀ t ≥ N,
      min (u r) (u t) - A * (min r t : ℝ)^(-β) ≤ u (r + t))
    (hnext : u s - A * (s : ℝ)^(-β) ≤ u (s + 1)) :
    ∀ q : ℕ, 1 ≤ q → ∀ r : ℕ, r ≤ q →
      u s - A * (s : ℝ)^(-β) -
        A * balanceConstant β * (s : ℝ)^(-β) * (1 - (q : ℝ)^(-β)) ≤ u (q * s + r) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq r hr
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    have hpow : 0 ≤ (s : ℝ)^(-β) := (Real.rpow_pos_of_pos hs' _).le
    have hcoef : 0 ≤ A * balanceConstant β * (s : ℝ)^(-β) :=
      mul_nonneg (mul_nonneg hA (balanceConstant_pos hβ).le) hpow
    by_cases hq1 : q = 1
    · subst q
      have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with hr0 | hr1
      · subst r
        simp only [Nat.cast_one, Real.one_rpow, sub_self, mul_zero, sub_zero, one_mul, add_zero]
        exact sub_le_self _ (mul_nonneg hA hpow)
      · subst r
        simpa only [Nat.cast_one, Real.one_rpow, sub_self, mul_zero, sub_zero, one_mul] using hnext
    · have hq2 : 2 ≤ q := by omega
      let a := q / 2
      let b := q - a
      let r₁ := min r a
      let r₂ := r - r₁
      have ha : 1 ≤ a := by dsimp [a]; omega
      have hb : 1 ≤ b := by dsimp [b, a]; omega
      have haq : a < q := by dsimp [a]; omega
      have hbq : b < q := by dsimp [b, a]; omega
      have hab : a ≤ b := by dsimp [a, b]; omega
      have habq : a + b = q := by dsimp [b, a]; omega
      have hqa : q ≤ 3 * a := by dsimp [a]; omega
      have hbq' : 3 * b ≤ 2 * q := by dsimp [b, a]; omega
      have hr₁ : r₁ ≤ a := min_le_right r a
      have hr₂ : r₂ ≤ b := by dsimp [r₂, r₁, b]; omega
      have hrr : r₁ + r₂ = r := by dsimp [r₂, r₁]; omega
      have hiA := ih a haq ha r₁ hr₁
      have hiB := ih b hbq hb r₂ hr₂
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hb' : (0 : ℝ) < b := by exact_mod_cast hb
      have hq' : (0 : ℝ) < q := by exact_mod_cast hq
      have habpow : (b : ℝ)^(-β) ≤ (a : ℝ)^(-β) :=
        Real.rpow_le_rpow_of_nonpos ha' (by exact_mod_cast hab) (neg_nonpos.mpr hβ.le)
      have hchild : u s - A * (s : ℝ)^(-β) -
          A * balanceConstant β * (s : ℝ)^(-β) * (1 - (b : ℝ)^(-β)) ≤
          min (u (a * s + r₁)) (u (b * s + r₂)) := by
        apply le_min
        · have hh := mul_le_mul_of_nonneg_left habpow hcoef
          nlinarith
        · exact hiB
      have hsizeA : N ≤ a * s + r₁ := by nlinarith
      have hsizeB : N ≤ b * s + r₂ := by nlinarith
      have hsize : a * s ≤ min (a * s + r₁) (b * s + r₂) := by
        apply le_min <;> nlinarith
      have hminpos : (0 : ℝ) < (a : ℝ) * s := mul_pos ha' hs'
      have hminpow := Real.rpow_le_rpow_of_nonpos hminpos
        (show (a : ℝ) * s ≤ (min (a * s + r₁) (b * s + r₂) : ℝ) by exact_mod_cast hsize)
        (neg_nonpos.mpr hβ.le)
      rw [Real.mul_rpow ha'.le hs'.le] at hminpow
      have herr := mul_le_mul_of_nonneg_left hminpow hA
      have hpotential := balanced_power_potential hβ hb' hq'
        (show (q : ℝ) / 3 ≤ a by
          have hh : (q : ℝ) ≤ 3 * a := by exact_mod_cast hqa
          linarith)
        (show (b : ℝ) ≤ q / (3 / 2) by
          have hh : 3 * (b : ℝ) ≤ 2 * q := by exact_mod_cast hbq'
          linarith)
      have hpot := mul_le_mul_of_nonneg_left hpotential (mul_nonneg hA hpow)
      have hc := hadd (a * s + r₁) hsizeA (b * s + r₂) hsizeB
      have he : a * s + r₁ + (b * s + r₂) = q * s + r := by
        calc
          _ = (a + b) * s + (r₁ + r₂) := by ring
          _ = _ := by rw [habq, hrr]
      rw [he] at hc
      simp only [Nat.cast_add, Nat.cast_mul] at hc
      nlinarith

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.balanced_blocks_bound := @_root_.OAI.FixedClauseThreshold.balanced_blocks_bound
