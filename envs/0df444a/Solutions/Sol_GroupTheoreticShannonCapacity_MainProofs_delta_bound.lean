-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.delta_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:46.108621+00:00
-- url     : https://prove2.me/submissions/bcd9a527-a03d-4647-8507-39b240a56f98

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (n k b r s : ℝ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) (hkb : k ≤ b)
    (hr_nonneg : 0 ≤ r) (hrb : r ≤ b)
    (hs_nonneg : 0 ≤ s) (hsbn : s ≤ b ^ n) :
    Delta n k b r s ≤ 6 * b^2 / n := by
  -- Following the paper's proof of Lemma 4.6 (lem:Delta_bound)
  -- The proof uses the Bernoulli inequality (1+x)^(1/n) ≤ 1 + x/n for x ≥ 0, n ≥ 1
  simp only [Delta]
  -- Define a = k·b^n + s·b + r
  set a := k * b ^ n + s * b + r with ha_def
  -- Key positivity facts
  have hb_pos : 0 < b := by linarith
  have hn_pos : 0 < n := by linarith
  have hk_pos : 0 < k := by linarith
  have hbn_pos : 0 < b ^ n := Real.rpow_pos_of_pos hb_pos n
  have hbn1_pos : 0 < b ^ (n + 1) := Real.rpow_pos_of_pos hb_pos (n + 1)
  -- Common power identities (proven once, used multiple times)
  have hbn_mul_b : b ^ n * b = b ^ (n + 1) := by
    have h1 : b ^ n * b = b ^ n * b ^ (1 : ℝ) := by rw [Real.rpow_one]
    have h2 : b ^ n * b ^ (1 : ℝ) = b ^ (n + 1) := by rw [Real.rpow_add hb_pos]
    rw [h1, h2]
  have hb_mul_bn : b * b ^ n = b ^ (n + 1) := by rw [mul_comm, hbn_mul_b]
  have hb_le_bn : b ≤ b ^ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le hb hn
  have hbn_le_bn1 : b ^ n ≤ b ^ (n + 1) := Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  have ha_pos : 0 < a := by
    have h1 : 0 < k * b ^ n := mul_pos hk_pos hbn_pos
    have h2 : 0 ≤ s * b := mul_nonneg hs_nonneg (le_of_lt hb_pos)
    linarith
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  -- The term r/k * s^n is non-negative
  have hrk_sn_nonneg : 0 ≤ r / k * s ^ n := by
    apply mul_nonneg
    · exact div_nonneg hr_nonneg (le_of_lt hk_pos)
    · exact Real.rpow_nonneg hs_nonneg n
  -- The denominator r/k + b^n is positive
  have hdenom_pos : 0 < r / k + b ^ n := by
    have : 0 ≤ r / k := div_nonneg hr_nonneg (le_of_lt hk_pos)
    linarith
  -- Step 1: Δ ≤ a/b - (a^n/(r/k + b^n))^(1/n)  (drop the non-negative r/k·s^n term)
  have h1n_pos : 0 < 1 / n := by positivity
  have h1n_nonneg : 0 ≤ 1 / n := le_of_lt h1n_pos
  have step1 : a / b - ((r / k * s ^ n + a ^ n) / (r / k + b ^ n)) ^ (1 / n) ≤
               a / b - (a ^ n / (r / k + b ^ n)) ^ (1 / n) := by
    -- Adding r/k·s^n ≥ 0 to numerator increases the fraction, hence the 1/n power
    -- So subtracting gives a smaller result
    apply sub_le_sub_left
    apply Real.rpow_le_rpow
    · exact div_nonneg (Real.rpow_nonneg ha_nonneg n) (le_of_lt hdenom_pos)
    · apply div_le_div_of_nonneg_right _ (le_of_lt hdenom_pos)
      have han_nonneg : 0 ≤ a ^ n := Real.rpow_nonneg ha_nonneg n
      linarith
    · exact h1n_nonneg
  -- The rest of the proof involves:
  -- Step 2: Factor as (a/b)[1 - 1/(1+x)^(1/n)] where x = r/(kb^n)
  -- Step 3: Use Bernoulli: 1 - 1/(1+x)^(1/n) ≤ x/n for x ≥ 0
  -- Step 4: Bound a/b and r/(kb^n) to get final result
  -- This requires careful real analysis lemmas about power functions
  calc a / b - ((r / k * s ^ n + a ^ n) / (r / k + b ^ n)) ^ (1 / n)
      ≤ a / b - (a ^ n / (r / k + b ^ n)) ^ (1 / n) := step1
    _ ≤ 6 * b ^ 2 / n := by
        -- Technical real analysis proof using Bernoulli inequality
        -- Key insight: rewrite as (a/b)(1 - 1/(1+x)^(1/n)) where x = r/(kb^n)
        -- Then use Bernoulli to bound 1 - 1/(1+x)^(1/n) ≤ x/n
        -- Finally bound a and x to get the result

        -- Step 2: Simplify (a^n / D)^(1/n) = a / D^(1/n) for D = r/k + b^n
        have han_pos : 0 < a ^ n := Real.rpow_pos_of_pos ha_pos n
        have han_div : (a ^ n / (r / k + b ^ n)) ^ (1 / n) =
            a / (r / k + b ^ n) ^ (1 / n) := by
          rw [Real.div_rpow (le_of_lt han_pos) (le_of_lt hdenom_pos)]
          congr 1
          rw [← Real.rpow_mul (le_of_lt ha_pos), mul_one_div_cancel (ne_of_gt hn_pos),
              Real.rpow_one]
        -- Step 3: Rewrite as (a/b)(1 - b/(r/k + b^n)^(1/n))
        have hdenom_1n_pos : 0 < (r / k + b ^ n) ^ (1 / n) :=
          Real.rpow_pos_of_pos hdenom_pos (1 / n)
        have hb_div_denom : b / (r / k + b ^ n) ^ (1 / n) =
            1 / (1 + r / (k * b ^ n)) ^ (1 / n) := by
          -- r/k + b^n = b^n(1 + r/(kb^n))
          have hfactor : r / k + b ^ n = b ^ n * (1 + r / (k * b ^ n)) := by
            have hkbn_pos : 0 < k * b ^ n := mul_pos hk_pos hbn_pos
            field_simp
            ring
          rw [hfactor]
          rw [Real.mul_rpow (le_of_lt hbn_pos) (by positivity)]
          -- b^n^(1/n) = b
          have hbn_1n : (b ^ n) ^ (1 / n) = b := by
            rw [← Real.rpow_mul (le_of_lt hb_pos)]
            rw [mul_one_div_cancel (ne_of_gt hn_pos), Real.rpow_one]
          rw [hbn_1n]
          rw [div_mul_eq_div_div, div_self (ne_of_gt hb_pos)]
        rw [han_div]
        -- Now we have a/b - a/D^(1/n) = (a/b)(1 - b/D^(1/n))
        have hfactor_expr : a / b - a / (r / k + b ^ n) ^ (1 / n) =
            (a / b) * (1 - b / (r / k + b ^ n) ^ (1 / n)) := by
          have hb_ne : b ≠ 0 := ne_of_gt hb_pos
          have hd_ne : (r / k + b ^ n) ^ (1 / n) ≠ 0 := ne_of_gt hdenom_1n_pos
          field_simp [hb_ne, hd_ne]
        rw [hfactor_expr, hb_div_denom]
        -- Step 4: Use Bernoulli inequality
        -- (1 + x)^(1/n) ≤ 1 + x/n for 0 ≤ 1/n ≤ 1 and x ≥ -1
        -- So 1/(1+x)^(1/n) ≥ 1/(1 + x/n)
        -- So 1 - 1/(1+x)^(1/n) ≤ 1 - 1/(1 + x/n) = (x/n)/(1 + x/n) ≤ x/n
        set x := r / (k * b ^ n) with hx_def
        have hx_nonneg : 0 ≤ x := by
          apply div_nonneg hr_nonneg
          exact mul_pos hk_pos hbn_pos |>.le
        have hx_ge_neg1 : -1 ≤ x := by linarith
        have h1n_le1 : 1 / n ≤ 1 := by
          rw [div_le_one hn_pos]
          exact hn
        -- Apply Bernoulli: (1 + x)^(1/n) ≤ 1 + x/n
        have hbernoulli := rpow_one_add_le_one_add_mul_self hx_ge_neg1 h1n_nonneg h1n_le1
        -- hbernoulli : (1 + x)^(1/n) ≤ 1 + (1/n) * x = 1 + x/n
        have h1x_pos : 0 < 1 + x := by linarith
        have h1xn_pos : 0 < (1 + x) ^ (1 / n) := Real.rpow_pos_of_pos h1x_pos (1 / n)
        have h1xn_div_pos : 0 < 1 + x / n := by
          have : 0 ≤ x / n := div_nonneg hx_nonneg (le_of_lt hn_pos)
          linarith
        -- 1 - 1/(1+x)^(1/n) ≤ x/n
        have hbound1 : 1 - 1 / (1 + x) ^ (1 / n) ≤ x / n := by
          -- From (1+x)^(1/n) ≤ 1 + x/n, we get 1/(1+x)^(1/n) ≥ 1/(1 + x/n)
          have hinv : 1 / (1 + x / n) ≤ 1 / (1 + x) ^ (1 / n) := by
            apply one_div_le_one_div_of_le h1xn_pos
            calc (1 + x) ^ (1 / n) ≤ 1 + (1 / n) * x := hbernoulli
              _ = 1 + x / n := by ring
          -- So 1 - 1/(1+x)^(1/n) ≤ 1 - 1/(1 + x/n) = (x/n)/(1 + x/n)
          have h1_sub : 1 - 1 / (1 + x) ^ (1 / n) ≤ 1 - 1 / (1 + x / n) := by linarith
          -- 1 - 1/(1 + x/n) = (x/n)/(1 + x/n)
          have hsimp : 1 - 1 / (1 + x / n) = (x / n) / (1 + x / n) := by field_simp; ring
          rw [hsimp] at h1_sub
          -- (x/n)/(1 + x/n) ≤ x/n since 1 + x/n ≥ 1
          have h_one_le : 1 ≤ 1 + x / n := by
            have : 0 ≤ x / n := div_nonneg hx_nonneg (le_of_lt hn_pos)
            linarith
          have hfinal : (x / n) / (1 + x / n) ≤ x / n := by
            apply div_le_self (div_nonneg hx_nonneg (le_of_lt hn_pos))
            exact h_one_le
          linarith
        -- Step 5: Bound a/b and x to get the final result
        -- (a/b)(1 - 1/(1+x)^(1/n)) ≤ (a/b)(x/n) = ax/(bn) = ar/(knb^(n+1))
        have hmain : (a / b) * (1 - 1 / (1 + x) ^ (1 / n)) ≤ (a / b) * (x / n) := by
          apply mul_le_mul_of_nonneg_left hbound1
          exact div_nonneg ha_nonneg (le_of_lt hb_pos)
        -- Now bound ar/(knb^(n+1)) ≤ 6b²/n
        -- Using a ≤ 3b^(n+1) and r ≤ b, k ≥ 1
        have ha_bound : a ≤ 3 * b ^ (n + 1) := by
          -- a = kb^n + sb + r ≤ kb^n + b^n·b + b = kb^n + b^(n+1) + b
          have hs_bound : s * b ≤ b ^ n * b := mul_le_mul_of_nonneg_right hsbn (le_of_lt hb_pos)
          have hr_bound : r ≤ b := hrb
          rw [hbn_mul_b] at hs_bound
          -- kb^n ≤ b·b^n = b^(n+1) since k ≤ b
          have hkbn_bound : k * b ^ n ≤ b * b ^ n :=
            mul_le_mul_of_nonneg_right hkb (le_of_lt hbn_pos)
          rw [hb_mul_bn] at hkbn_bound
          calc a = k * b ^ n + s * b + r := ha_def
            _ ≤ b ^ (n + 1) + b ^ (n + 1) + b := by linarith
            _ ≤ b ^ (n + 1) + b ^ (n + 1) + b ^ n := by linarith [hb_le_bn]
            _ ≤ b ^ (n + 1) + b ^ (n + 1) + b ^ (n + 1) := by linarith
            _ = 3 * b ^ (n + 1) := by ring
        -- x = r/(kb^n) ≤ b/(1·b^n) = b/b^n ≤ 1 for n ≥ 1
        have hx_bound : x ≤ 1 := by
          rw [hx_def]
          have hstep1 : r / (k * b ^ n) ≤ b / b ^ n := by
            apply div_le_div₀ (le_of_lt hb_pos) hrb hbn_pos
            simpa using mul_le_mul_of_nonneg_right hk (le_of_lt hbn_pos)
          calc r / (k * b ^ n) ≤ b / b ^ n := hstep1
            _ ≤ 1 := by rw [div_le_one hbn_pos]; exact hb_le_bn
        -- Final calculation
        calc (a / b) * (1 - 1 / (1 + x) ^ (1 / n))
            ≤ (a / b) * (x / n) := hmain
          _ = a * r / (k * b ^ (n + 1) * n) := by
              rw [hx_def]; field_simp [ne_of_gt hb_pos, ne_of_gt hn_pos]; rw [← hb_mul_bn]; ring
          _ ≤ (3 * b ^ (n + 1)) * b / (k * b ^ (n + 1) * n) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul ha_bound hrb hr_nonneg (by linarith)
          _ = 3 * b / (k * n) := by
              field_simp [ne_of_gt hbn1_pos, ne_of_gt hk_pos, ne_of_gt hn_pos]
          _ ≤ 3 * b / (1 * n) := by
              apply div_le_div_of_nonneg_left (by linarith) (by positivity)
              exact mul_le_mul hk (le_refl _) (le_of_lt hn_pos) (by linarith)
          _ = 3 * b / n := by ring
          _ ≤ 6 * b ^ 2 / n := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hn_pos)
              have hb_sq : b ≤ b ^ 2 := by nlinarith [sq_nonneg b]
              linarith
end GroupTheoreticShannonCapacity.MainProofs
