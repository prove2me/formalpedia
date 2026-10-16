-- Prove2me | solution 1 for OAI.RandomKSAT.replacement_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:49:54.92518+00:00
-- url     : https://prove2.me/submissions/e3734c32-7591-4e97-ba28-166b623e83c9

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BlockKilling.lean:L204-L275
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.replacement_numeric. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Theorems.Thm_OAI_RandomKSAT_frozen_power
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

lemma killRatio_eq_zero {u b s : ℕ} (hbs : b < s) : killRatio u b s = 0 := by
  simp [killRatio, Nat.choose_eq_zero_of_lt hbs]

lemma killRatio_le_half_pow {u b s : ℕ} (hu : 0 < u) (hbu : b ≤ u) (hsu : s ≤ u) :
    killRatio u b s ≤ ((1 : ℝ)/2)^s := by
  apply (killRatio_le_density_pow hbu hsu).trans
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*u)).2
  have hb : (b : ℝ) ≤ u := by exact_mod_cast hbu
  nlinarith

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BlockKilling ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma one_sub_exp_neg_two_mul_ge {h : ℝ} (h₀ : 0 ≤ h) (h₁ : h ≤ 1/2) :
    h ≤ 1-Real.exp (-2*h) := by
  have hre : Real.exp (-2*h) ≤ (1+2*h)⁻¹ := by
    have he := Real.add_one_le_exp (2*h)
    rw [show -2*h = -(2*h) by ring, Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith)
  have hi : (1+2*h)⁻¹ ≤ 1-h := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1+2*h)).2
    nlinarith
  linarith

lemma replacementK_succ (r : ℕ) : replacementK (r+1) = ((2 : ℝ)^(r+1)*r)^r := by
  simp [replacementK]

lemma replacement_numeric {u b r g : ℕ} (hr : 2 ≤ r) (hbu : b ≤ u)
    (hru : r+1 ≤ u) (hg : 1 ≤ g) {R : ℝ} (hR : 0 ≤ R)
    (hind : 1-Real.exp (-(g : ℝ)*killRatio u b (r+1)) ≤ R)
    (hlong : (2 : ℝ)^(r+2)*u ≤ g → (1 : ℝ)/3 ≤ R) :
    killRatio u b r - replacementK (r+1)/(g : ℝ)^r ≤ R := by
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hu₀ : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hquarter : killRatio u b r ≤ 1/4 := by
    apply (killRatio_le_half_pow (by omega) hbu (by omega)).trans
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num) hr
    norm_num at h ⊢
    exact h
  have hK : (2 : ℝ)*(r+1) ≤ (2 : ℝ)^(r+1)*r := by
    have h2 : (4 : ℝ) ≤ (2 : ℝ)^(r+1) := by
      calc
        _ = (2 : ℝ)^2 := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    nlinarith
  rw [replacementK_succ, ← div_pow]
  by_cases hrb : r+1 ≤ b
  · by_cases hlarge : 2 ≤ (g : ℝ)/(r+1) * (killRatio u b r)^((r : ℝ)⁻¹)
    · have hp := frozen_power (by omega : 1 ≤ r) hbu hrb
      have hex : ((r : ℝ)+1)/r = 1+(r : ℝ)⁻¹ := by field_simp
      rw [hex, Real.rpow_add_of_nonneg (killRatio_nonneg u b r) zero_le_one
        (by positivity), Real.rpow_one] at hp
      have hs : 2*killRatio u b r ≤ (g : ℝ)*killRatio u b (r+1) := by
        have h₁ := mul_le_mul_of_nonneg_left hlarge (killRatio_nonneg u b r)
        have h₂ := mul_le_mul_of_nonneg_left hp hg₀.le
        calc
          2*killRatio u b r = killRatio u b r*2 := by ring
          _ ≤ killRatio u b r * ((g : ℝ)/(r+1) * (killRatio u b r)^((r : ℝ)⁻¹)) := h₁
          _ = (g : ℝ) * (killRatio u b r * (killRatio u b r)^((r : ℝ)⁻¹)/(r+1)) := by ring
          _ ≤ _ := h₂
      have ht := Real.exp_le_exp.mpr (neg_le_neg hs)
      simp only [← neg_mul] at ht
      have hh := one_sub_exp_neg_two_mul_ge (killRatio_nonneg u b r) (by linarith :
        killRatio u b r ≤ 1/2)
      have herr : 0 ≤ ((2:ℝ)^(r+1)*r/g)^r := by positivity
      linarith
    · have hroot : (killRatio u b r)^((r : ℝ)⁻¹) ≤ 2*(r+1)/(g : ℝ) := by
        apply (le_div_iff₀ hg₀).2
        have hh := (not_le.mp hlarge).le
        rw [div_mul_eq_mul_div] at hh
        have hh' := (div_le_iff₀ (by positivity : (0:ℝ)<r+1)).mp hh
        linarith
      have hbound : killRatio u b r ≤ ((2:ℝ)^(r+1)*r/g)^r := by
        calc
          killRatio u b r = ((killRatio u b r)^((r : ℝ)⁻¹))^r :=
            (Real.rpow_inv_natCast_pow (killRatio_nonneg u b r) (by omega : r ≠ 0)).symm
          _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg (killRatio_nonneg u b r) _)
            (hroot.trans (div_le_div_of_nonneg_right hK hg₀.le)) r
      linarith
  · by_cases hbr : b < r
    · rw [killRatio_eq_zero hbr]
      have herr : 0 ≤ ((2:ℝ)^(r+1)*r/g)^r := by positivity
      linarith
    · have hbr : b = r := by omega
      subst b
      by_cases hlong' : (2 : ℝ)^(r+2)*u ≤ g
      · have hh := hlong hlong'
        have herr : 0 ≤ ((2:ℝ)^(r+1)*r/g)^r := by positivity
        linarith
      · have hg' : (g : ℝ) ≤ (2 : ℝ)^(r+2)*u := (not_le.mp hlong').le
        have hd : (r : ℝ)/(2*u) ≤ (2 : ℝ)^(r+1)*r/g := by
          apply (div_le_div_iff₀ (by positivity) hg₀).2
          rw [show r+2 = (r+1)+1 by omega, pow_succ] at hg'
          nlinarith [mul_le_mul_of_nonneg_left hg' hr₀.le]
        have hh := (killRatio_le_density_pow hbu (by omega : r ≤ u)).trans
          (pow_le_pow_left₀ (by positivity) hd r)
        linarith

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.replacement_numeric := @_root_.OAI.RandomKSAT.replacement_numeric
