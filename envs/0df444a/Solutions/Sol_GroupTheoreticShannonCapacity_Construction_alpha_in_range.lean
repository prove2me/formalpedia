-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.alpha_in_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:45:14.053846+00:00
-- url     : https://prove2.me/submissions/133692f4-1bf5-464c-8b58-34ced96ad194

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b) :
    (r : ℚ) * s^n / (k * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n) ∈ Set.Icc 0 1 := by
  constructor
  · -- (rs^n)/(ka^n) ≥ 0: all terms are nonnegative
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg r) (pow_nonneg (Nat.cast_nonneg s) n)
    · -- a n k b r s = k*b^n + s*b + r ≥ 0 for natural number inputs
      have ha_pos : (0 : ℚ) ≤ a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) := by
        simp only [a]
        positivity
      exact mul_nonneg (Nat.cast_nonneg k) (pow_nonneg ha_pos n)
  · -- (rs^n)/(ka^n) ≤ 1: equivalent to rs^n ≤ ka^n
    -- From paper (line 933): rs^n ≤ bs^n ≤ (bs)^n ≤ a^n ≤ ka^n
    -- First handle the trivial case where the denominator might be 0
    by_cases hka : (k : ℚ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n = 0
    · -- If ka^n = 0, the fraction is 0 (or undefined, but we handle it as ≤ 1)
      simp [hka]
    · -- ka^n > 0, so we can use div_le_one
      have ha_pos : (0 : ℚ) < a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) := by
        simp only [a]
        positivity
      have hka_pos : (0 : ℚ) < (k : ℚ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n := by
        have hk_pos : (0 : ℚ) < k := by positivity
        have han_pos : (0 : ℚ) < (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^n := pow_pos ha_pos n
        exact mul_pos hk_pos han_pos
      rw [div_le_one hka_pos]
      -- Goal: (r : ℚ) * s^n ≤ k * a^n
      -- Prove the chain: rs^n ≤ bs^n ≤ (bs)^n ≤ a^n ≤ ka^n
      -- Step 1: rs^n ≤ bs^n (since r ≤ b)
      have h1 : (r : ℚ) * s^n ≤ b * s^n := by
        have : (r : ℚ) ≤ b := by exact_mod_cast hrb
        exact mul_le_mul_of_nonneg_right this (pow_nonneg (Nat.cast_nonneg s) n)
      -- Step 2: bs^n ≤ (bs)^n (since b ≥ 1 implies b ≤ b^n when n ≥ 1)
      have h2 : (b : ℚ) * (s : ℚ)^n ≤ ((b : ℚ) * (s : ℚ))^n := by
        by_cases hs : s = 0
        · -- Case s = 0: both sides are 0
          simp [hs, zero_pow (by omega : n ≠ 0)]
        · -- Case s ≠ 0: use b ≤ b^n and multiply by s^n
          have hs_pos : (0 : ℚ) < s := by positivity
          have hsn_pos : (0 : ℚ) < (s : ℚ)^n := pow_pos hs_pos n
          rw [mul_pow]
          have hb_ge_one : (1 : ℚ) ≤ b := by exact_mod_cast hb
          have hbn_ge_b : (b : ℚ) ≤ (b : ℚ)^n := by
            calc (b : ℚ) = (b : ℚ)^1 := (pow_one (b : ℚ)).symm
              _ ≤ (b : ℚ)^n := pow_le_pow_right₀ hb_ge_one hn
          exact mul_le_mul_of_nonneg_right hbn_ge_b (le_of_lt hsn_pos)
      -- Step 3: (bs)^n ≤ a^n (since bs ≤ a)
      have h3 : ((b : ℚ) * (s : ℚ))^n ≤ ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) : ℚ)^n := by
        -- bs ≤ a = kb^n + sb + r, then use pow monotonicity
        have hbs_le_a : (b : ℚ) * (s : ℚ) ≤ (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℚ) := by
          simp only [a]; push_cast
          have hbn_pos : (0:ℚ) < (b:ℚ)^n := pow_pos (by positivity : (0:ℚ) < b) n
          nlinarith [hbn_pos, (show (1:ℚ) ≤ k by exact_mod_cast hk), (show (0:ℚ) ≤ r by positivity)]
        exact pow_le_pow_left₀ (by positivity) hbs_le_a n
      -- Step 4: a^n ≤ ka^n (since k ≥ 1)
      have h4 : ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) : ℚ)^n ≤
                (k : ℚ) * ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) : ℚ)^n := by
        have hk_ge_one : (1 : ℚ) ≤ k := by exact_mod_cast hk
        have han_nonneg : (0 : ℚ) ≤ ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) : ℚ)^n :=
          pow_nonneg (le_of_lt ha_pos) n
        calc ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) : ℚ)^n
              = 1 * ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) : ℚ)^n := (one_mul _).symm
          _ ≤ k * ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) : ℚ)^n :=
              mul_le_mul_of_nonneg_right hk_ge_one han_nonneg
      -- Combine the chain
      calc (r : ℚ) * s^n ≤ b * s^n := h1
        _ ≤ (b * s)^n := h2
        _ ≤ ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) : ℚ)^n := h3
        _ ≤ k * ((a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) : ℚ)^n := h4
end GroupTheoreticShannonCapacity.Construction
