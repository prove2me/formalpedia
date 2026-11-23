-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.alpha_real_in_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:24.345616+00:00
-- url     : https://prove2.me/submissions/9420e1d8-f537-4133-8a27-bd0c0fb1cb66

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r : ℕ) (s : ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) (hs : 0 < s) :
    (r : ℝ) * s^n / (k * (aReal n k b r s)^n) ∈ Set.Icc 0 1 := by
  have ha_pos : 0 < aReal n k b r s := by unfold aReal; positivity
  constructor
  · -- Show ≥ 0
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg r) (pow_nonneg (le_of_lt hs) n)
    · apply mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (le_of_lt ha_pos) n)
  · -- Show ≤ 1
    -- Chain: r*s^n ≤ b*s^n ≤ (b*s)^n ≤ a^n ≤ k*a^n
    have hka_pos : 0 < (k : ℝ) * (aReal n k b r s)^n := by
      apply mul_pos
      · positivity
      · exact pow_pos ha_pos n
    rw [div_le_one hka_pos]
    have h1 : (r : ℝ) * s^n ≤ (b : ℝ) * s^n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_of_lt hs) n)
      exact_mod_cast hrb
    have hbs_le_a : (b : ℝ) * s ≤ aReal n k b r s := by
      unfold aReal
      have hterm1 : 0 ≤ (k : ℝ) * (b : ℝ)^n := by positivity
      have hterm2 : 0 ≤ (r : ℝ) := by positivity
      linarith
    have hb_pos : 0 < (b : ℝ) := by positivity
    have hbs_pos : 0 < (b : ℝ) * s := mul_pos hb_pos hs
    have hb_ge_one : 1 ≤ (b : ℝ) := by exact_mod_cast hb
    have h2 : (b : ℝ) * s^n ≤ (aReal n k b r s)^n := by
      have hb_le_bn : (b : ℝ) ≤ (b : ℝ)^n := by
        calc (b : ℝ) = (b : ℝ)^1 := (pow_one _).symm
          _ ≤ (b : ℝ)^n := pow_le_pow_right₀ hb_ge_one (by omega : 1 ≤ n)
      calc (b : ℝ) * s^n ≤ (b : ℝ)^n * s^n := by nlinarith [pow_nonneg (le_of_lt hs) n]
        _ = ((b : ℝ) * s)^n := by rw [mul_pow]
        _ ≤ (aReal n k b r s)^n := pow_le_pow_left₀ (le_of_lt hbs_pos) hbs_le_a n
    have h3 : (aReal n k b r s)^n ≤ (k : ℝ) * (aReal n k b r s)^n := by
      apply le_mul_of_one_le_left (pow_nonneg (le_of_lt ha_pos) n)
      exact_mod_cast hk
    linarith
end GroupTheoreticShannonCapacity.Construction
