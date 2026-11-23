-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.subgroup_capacity_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:11.250886+00:00
-- url     : https://prove2.me/submissions/f85bc25a-e21f-4e93-868c-7e0d5e0e67a3

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_delta_bound
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_construction_addSubgroupCapacity_bound
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_p_over_q_le_a_over_b
import Theorems.Thm_GroupTheoreticShannonCapacity_addSubgroupShannonCapacity_le_shannonCapacity
import Theorems.Thm_GroupTheoreticShannonCapacity_addSubgroupShannonCapacity_lift
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_fractionGraph_le


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
set_option maxHeartbeats 300000
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ p q : ℕ, p ≠ 0 → 0 < q → (p : ℝ) / q > M →
      ∃ (a b : ℕ) (_ : NeZero a), (a : ℚ) / b = (p : ℚ) / q ∧
        (p : ℝ) / q - addSubgroupShannonCapacity (fractionGraph a b) < ε := by
  /-
  Proof strategy (from Section 4 of the paper):
  1. Choose base b ≈ 2/ε and power n such that 6b²/n < ε/2
  2. Decompose the target fraction to get construction parameters
  3. construction_lower_bound gives AddSubgroup S in E_{p'/q'}^⊠n with |S| ≥ p'
  4. Therefore addSubgroupShannonCapacity(E_{p'/q'}) ≥ p'^(1/n)
  5. By addSubgroupShannonCapacity_lift: transfer bound to E_{a/b} with a/b = p/q
  6. delta_bound shows: a/b - p'^(1/n) ≤ 6b²/n < ε
  -/

  -- Choose base b and power n based on ε (following paper's proof of Theorem 1.4)
  let b_for_small_ε := Nat.ceil (2 / ε) + 1
  let n_needed := Nat.ceil (12 * (b_for_small_ε : ℝ)^2 / ε) + 1
  -- M needs to be large enough for the construction to give good bounds
  use max 5 ((b_for_small_ε : ℝ)^n_needed)
  intro p q hp_ne hq_pos hpq_large
  have hp_pos : 0 < p := Nat.pos_of_ne_zero hp_ne
  -- Use general base b = b_for_small_ε = ⌈2/ε⌉ + 1 instead of base 2.
  -- This gives gap bounds that are O(ε), not O(m).
  -- Step 1: Set up base b and define a'' = ⌊b * p / q⌋
  set b := b_for_small_ε with hb_def
  have hb_pos : 0 < b := by
    simp only [b, b_for_small_ε]
    have : Nat.ceil (2 / ε) + 1 ≥ 1 := Nat.le_add_left 1 _
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 1) this
  have hb_gt_1 : 1 < b := by
    simp only [b, b_for_small_ε]
    have : Nat.ceil (2 / ε) + 1 ≥ 2 := by
      have h_ceil : 0 ≤ Nat.ceil (2 / ε) := Nat.zero_le _
      calc 2 = 1 + 1 := by norm_num
        _ ≤ Nat.ceil (2 / ε) + 1 := Nat.add_le_add_right (Nat.one_le_iff_ne_zero.mpr
            (Nat.ceil_pos.mpr (by positivity : 0 < 2 / ε)).ne') 1
    exact Nat.lt_of_lt_of_le (by norm_num : 1 < 2) this
  -- Cache common positivity facts for reuse
  have hq_pos_real : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hb_pos_real : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hq_ne_real : (q : ℝ) ≠ 0 := ne_of_gt hq_pos_real
  have hb_ne_real : (b : ℝ) ≠ 0 := ne_of_gt hb_pos_real
  -- a'' = ⌊b * p / q⌋, the approximation of b * p / q from below
  set a'' := b * p / q with ha''_def
  have ha''_pos : 0 < a'' := by
    -- b * p / q > 0 since b ≥ 2 and p/q > 5
    have h5 : (5 : ℝ) ≤ max 5 ((b_for_small_ε : ℝ)^n_needed) := le_max_left _ _
    have hpq_gt_5 : (5 : ℝ) < (p : ℝ) / q := lt_of_le_of_lt h5 hpq_large
    have hpq_gt_1 : (1 : ℝ) < (p : ℝ) / q := by linarith
    have hp_gt_q : q < p := by
      rw [one_lt_div hq_pos_real] at hpq_gt_1
      exact_mod_cast hpq_gt_1
    -- b * p / q ≥ b since p/q > 1
    have h1 : b ≤ b * p / q := by
      apply Nat.le_div_iff_mul_le hq_pos |>.mpr
      exact Nat.mul_le_mul_left b (le_of_lt hp_gt_q)
    exact Nat.lt_of_lt_of_le hb_pos h1
  have ha''_ne : a'' ≠ 0 := Nat.pos_iff_ne_zero.mp ha''_pos
  haveI : NeZero a'' := ⟨ha''_ne⟩
  -- Step 2: Show p/q - a''/b < 1/b < ε/2
  have hpq_a''_lt_eps_half : (p : ℝ) / q - (a'' : ℝ) / b < ε / 2 := by
    -- First: p/q - a''/b < 1/b (since a'' = ⌊b*p/q⌋)
    have h1 : (p : ℝ) / q - (a'' : ℝ) / b < 1 / b := by
      -- a'' = ⌊b*p/q⌋, so b*p/q - 1 < a'' ≤ b*p/q
      have h_lb : (b : ℝ) * p / q - 1 < a'' := by
        -- The remainder b*p % q < q, so b*p - q*(b*p/q) < q
        have h_rem_lt : b * p % q < q := Nat.mod_lt (b * p) hq_pos
        -- Also, b*p = q * (b*p/q) + b*p % q, so q*(b*p/q) ≤ b*p
        have h_div_mod : q * a'' + b * p % q = b * p := Nat.div_add_mod (b * p) q
        have hqa_le : q * a'' ≤ b * p := by linarith [Nat.zero_le (b * p % q)]
        -- b*p % q = b*p - q*a'' (natural subtraction)
        have h_mod_eq : b * p % q = b * p - q * a'' := by omega
        -- Cast to reals: (b*p : ℝ) - q*a'' < q
        have h'' : (b * p : ℝ) - (q : ℝ) * a'' < q := by
          have hcast : ((b * p - q * a'' : ℕ) : ℝ) = (b * p : ℝ) - (q : ℝ) * a'' := by
            rw [Nat.cast_sub hqa_le]; push_cast; ring
          rw [← hcast]
          have : ((b * p - q * a'' : ℕ) : ℝ) = ((b * p % q : ℕ) : ℝ) := by rw [h_mod_eq]
          rw [this]
          exact_mod_cast h_rem_lt
        -- Now show (b*p - q)/q < a'', i.e., b*p/q - 1 < a''
        -- We have (b*p : ℝ) - q*a'' < q, so b*p < q*a'' + q = q*(a'' + 1)
        -- Thus b*p/q < a'' + 1, so b*p/q - 1 < a''
        have h_key : (b : ℝ) * p < (q : ℝ) * (a'' + 1) := by linarith
        calc (b : ℝ) * p / q - 1 < ((q : ℝ) * (a'' + 1)) / q - 1 := by
              apply sub_lt_sub_right
              apply div_lt_div_of_pos_right h_key hq_pos_real
          _ = (a'' : ℝ) + 1 - 1 := by field_simp
          _ = a'' := by ring
      have h_ub : (a'' : ℝ) ≤ (b : ℝ) * p / q := by
        have h := Nat.div_mul_le_self (b * p) q
        have h' : a'' * q ≤ b * p := by exact h
        have h'' : (a'' : ℝ) * q ≤ (b : ℝ) * p := by exact_mod_cast h'
        calc (a'' : ℝ) = a'' * q / q := by field_simp
          _ ≤ (b : ℝ) * p / q := div_le_div_of_nonneg_right h'' (le_of_lt hq_pos_real)
      -- p/q - a''/b < 1/b using h_lb and h_ub
      -- From h_lb: b*p/q - 1 < a'', so b*p/q - a'' < 1
      -- From h_ub: a'' ≤ b*p/q, so b*p/q - a'' ≥ 0
      have hgap_bound : (b : ℝ) * p / q - a'' < 1 := by linarith
      have hgap_nonneg : 0 ≤ (b : ℝ) * p / q - a'' := by linarith
      -- (p/q - a''/b) = (b*p/q - a'')/b (after simplification)
      have heq : (p : ℝ) / q - (a'' : ℝ) / b = ((b : ℝ) * p / q - a'') / b := by
        field_simp [hq_ne_real, hb_ne_real]
      calc (p : ℝ) / q - (a'' : ℝ) / b = ((b : ℝ) * p / q - a'') / b := heq
        _ < 1 / b := by
            apply div_lt_div_of_pos_right hgap_bound hb_pos_real
    -- Second: 1/b < ε/2 (since b = ⌈2/ε⌉ + 1 > 2/ε)
    have h2 : 1 / (b : ℝ) < ε / 2 := by
      have hb_gt_2_eps : (b : ℝ) > 2 / ε := by
        simp only [b, b_for_small_ε]
        have h_ceil : (2 : ℝ) / ε ≤ Nat.ceil (2 / ε) := Nat.le_ceil _
        have hcast : ((Nat.ceil (2 / ε) + 1 : ℕ) : ℝ) = (Nat.ceil (2 / ε) : ℕ) + 1 := by
          push_cast; ring
        calc (b_for_small_ε : ℝ) = ((Nat.ceil (2 / ε) + 1 : ℕ) : ℝ) := by rfl
          _ = (Nat.ceil (2 / ε) : ℕ) + 1 := hcast
          _ > Nat.ceil (2 / ε) := by linarith
          _ ≥ 2 / ε := h_ceil
      calc 1 / (b : ℝ) < 1 / (2 / ε) := by
            apply one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 2 / ε) hb_gt_2_eps
        _ = ε / 2 := by field_simp
    linarith
  -- Step 3: Show a'' is large enough (a'' ≥ b^(n_needed+1))
  have ha''_large : b ^ (n_needed + 1) ≤ a'' := by
    -- p/q > b^n_needed from hpq_large
    have h1 : (b : ℝ) ^ n_needed < (p : ℝ) / q := by
      have h2 : ((b_for_small_ε : ℝ)^n_needed : ℝ) ≤
          max 5 ((b_for_small_ε : ℝ)^n_needed) := le_max_right _ _
      calc (b : ℝ) ^ n_needed = (b_for_small_ε : ℝ) ^ n_needed := by rfl
        _ ≤ max 5 ((b_for_small_ε : ℝ)^n_needed) := h2
        _ < (p : ℝ) / q := hpq_large
    -- Therefore b * p / q > b^(n_needed+1)
    have h2 : (b : ℝ) ^ (n_needed + 1) < (b : ℝ) * (p : ℝ) / q := by
      calc (b : ℝ) ^ (n_needed + 1) = (b : ℝ) * (b : ℝ) ^ n_needed := by ring
        _ < (b : ℝ) * ((p : ℝ) / q) := by
            apply mul_lt_mul_of_pos_left h1 hb_pos_real
        _ = (b : ℝ) * (p : ℝ) / q := by ring
    -- a'' = floor(b*p/q) ≥ b^(n_needed+1) since b^(n_needed+1) is an integer
    have h3 : (b ^ (n_needed + 1) : ℕ) ≤ b * p / q := by
      have h4 : ((b ^ (n_needed + 1) : ℕ) : ℝ) ≤ (b : ℝ) * (p : ℝ) / q := by
        have h5 : ((b ^ (n_needed + 1) : ℕ) : ℝ) = (b : ℝ) ^ (n_needed + 1) := by
          push_cast; rfl
        rw [h5]
        exact le_of_lt h2
      have h6 : (b ^ (n_needed + 1) : ℕ) * q ≤ b * p := by
        have h7 : ((b ^ (n_needed + 1) : ℕ) : ℝ) * q ≤ (b : ℝ) * (p : ℝ) := by
          calc ((b ^ (n_needed + 1) : ℕ) : ℝ) * q
              ≤ (b : ℝ) * (p : ℝ) / q * q := by
                apply mul_le_mul_of_nonneg_right h4 (le_of_lt hq_pos_real)
            _ = (b : ℝ) * (p : ℝ) := by field_simp
        exact_mod_cast h7
      exact Nat.le_div_iff_mul_le hq_pos |>.mpr h6
    exact h3
  -- Step 4: Define n'' = log_b(a'') and show n'' ≥ n_needed + 1
  set n'' := Nat.log b a'' with hn''_def
  have hn''_large : n_needed + 1 ≤ n'' := by
    rw [hn''_def]
    rw [Nat.le_log_iff_pow_le hb_gt_1 ha''_ne]
    exact ha''_large
  have hn''_ge1 : 1 ≤ n'' := by
    have : 1 ≤ n_needed + 1 := by omega
    omega
  have hn''_ne : n'' ≠ 0 := by omega
  haveI : NeZero n'' := ⟨hn''_ne⟩
  -- Step 5: Key bound: 6b²/n'' < ε/2
  have h6b2_n_lt : 6 * (b : ℝ)^2 / n'' < ε / 2 := by
    have hn_large_real : (n_needed + 1 : ℝ) ≤ n'' := by exact_mod_cast hn''_large
    have hn_needed_bound : (n_needed : ℝ) > 12 * (b : ℝ)^2 / ε := by
      simp only [n_needed]
      have h_ceil : 12 * (b_for_small_ε : ℝ)^2 / ε ≤
          Nat.ceil (12 * (b_for_small_ε : ℝ)^2 / ε) := Nat.le_ceil _
      calc ((Nat.ceil (12 * (b_for_small_ε : ℝ)^2 / ε) + 1 : ℕ) : ℝ)
          = (Nat.ceil (12 * (b_for_small_ε : ℝ)^2 / ε) : ℝ) + 1 := by push_cast; ring
        _ > 12 * (b_for_small_ε : ℝ)^2 / ε := by linarith
    have hn''_bound : (n'' : ℝ) > 12 * (b : ℝ)^2 / ε := by
      calc (n'' : ℝ) ≥ n_needed + 1 := hn_large_real
        _ > n_needed := by linarith
        _ > 12 * (b : ℝ)^2 / ε := hn_needed_bound
    have hn''_pos : 0 < (n'' : ℝ) := by exact_mod_cast (by omega : 0 < n'')
    have hb2_pos : 0 < (b : ℝ)^2 := by positivity
    -- 6b²/n'' < 6b² / (12b²/ε) = ε/2
    calc 6 * (b : ℝ)^2 / n''
        < 6 * (b : ℝ)^2 / (12 * (b : ℝ)^2 / ε) := by
          apply div_lt_div_of_pos_left (by positivity) (by positivity) hn''_bound
      _ = ε / 2 := by field_simp; ring
  -- Step 6: Decompose a'' = b^n'' + b*s'' + r'' with k=1
  have hbn_le : b ^ n'' ≤ a'' := Nat.pow_log_le_self b ha''_ne
  have ha''_lt : a'' < b ^ (n'' + 1) := Nat.lt_pow_succ_log_self hb_gt_1 a''
  set r'' := (a'' - b^n'') % b with hr''_def
  set s'' := (a'' - b^n'' - r'') / b with hs''_def
  have hr''_lt : r'' < b := Nat.mod_lt (a'' - b^n'') hb_pos
  have hr''_le : r'' ≤ b := Nat.le_of_lt hr''_lt
  have hr''_le_diff : r'' ≤ a'' - b^n'' := Nat.mod_le (a'' - b^n'') b
  -- Key property: a'' - b^n'' = b * s'' + r'' (standard division with remainder)
  have hdiff_eq : a'' - b^n'' = b * s'' + r'' := by
    have h1 : a'' - b^n'' = (a'' - b^n'' - r'') + r'' := by
      have := Nat.sub_add_cancel hr''_le_diff
      exact this.symm
    have h2 : (a'' - b^n'' - r'') = b * s'' := by
      simp only [hs''_def]
      have h := Nat.div_add_mod (a'' - b^n'' - r'') b
      have hmod : (a'' - b^n'' - r'') % b = 0 := by
        have hr_def : r'' = (a'' - b^n'') % b := rfl
        have h_div_add : b * ((a'' - b^n'') / b) + (a'' - b^n'') % b = a'' - b^n'' :=
          Nat.div_add_mod (a'' - b^n'') b
        have h_sub_eq : a'' - b^n'' - (a'' - b^n'') % b = (a'' - b^n'') / b * b := by
          have hmod_le : (a'' - b^n'') % b ≤ a'' - b^n'' := Nat.mod_le _ _
          have h_eq : (a'' - b^n'') / b * b = b * ((a'' - b^n'') / b) := Nat.mul_comm _ _
          calc a'' - b^n'' - (a'' - b^n'') % b
              = b * ((a'' - b^n'') / b) + (a'' - b^n'') % b - (a'' - b^n'') % b := by
                rw [h_div_add]
            _ = b * ((a'' - b^n'') / b) := by omega
            _ = (a'' - b^n'') / b * b := h_eq.symm
        rw [hr_def, h_sub_eq]
        have h_mul_comm : (a'' - b^n'') / b * b = b * ((a'' - b^n'') / b) := Nat.mul_comm _ _
        rw [h_mul_comm]
        exact Nat.mul_mod_right _ _
      rw [hmod, add_zero] at h
      exact h.symm
    rw [h1, h2]
  have hs''_le : s'' ≤ b ^ n'' := by
    have ha''_lt' : a'' < b * b^n'' := by
      calc a'' < b^(n'' + 1) := ha''_lt
        _ = b * b^n'' := pow_succ' b n''
    have hs''_le_quot : s'' ≤ (a'' - b^n'') / b := by
      simp only [hs''_def]
      apply Nat.div_le_div_right
      exact Nat.sub_le _ _
    have hdiff_lt : a'' - b^n'' < b * b^n'' := by
      calc a'' - b^n'' < b * b^n'' - b^n'' := Nat.sub_lt_sub_right hbn_le ha''_lt'
        _ ≤ b * b^n'' := Nat.sub_le _ _
    have hquot_le : (a'' - b^n'') / b ≤ b^n'' := by
      rw [Nat.div_le_iff_le_mul_add_pred hb_pos]
      have h1 : a'' - b^n'' < b * b^n'' + (b - 1) := by
        calc a'' - b^n'' < b * b^n'' := hdiff_lt
          _ ≤ b * b^n'' + (b - 1) := Nat.le_add_right _ _
      exact Nat.le_of_lt h1
    exact Nat.le_trans hs''_le_quot hquot_le
  -- Verify decomposition: b^n'' + b*s'' + r'' = a''
  have hdecomp : b^n'' + b * s'' + r'' = a'' := by
    calc b^n'' + b * s'' + r'' = b^n'' + (b * s'' + r'') := by ring
      _ = b^n'' + (a'' - b^n'') := by rw [hdiff_eq]
      _ = a'' := Nat.add_sub_cancel' hbn_le
  have hb_ge_1 : 1 ≤ b := Nat.one_le_of_lt hb_gt_1
  -- Step 7: Apply construction_addSubgroupCapacity_bound with general base b
  obtain ⟨p', q', hp'_ne, hq'_pos, hp'_eq, hq'_eq, hconstr⟩ :=
    construction_addSubgroupCapacity_bound n'' 1 b r'' s'' (by norm_num) hb_ge_1 hr''_le
  -- Step 8: Show p'/q' ≤ a''/b using p_over_q_le_a_over_b
  have hpq'_le : (p' : ℚ) / q' ≤ (a'' : ℚ) / b := by
    have h := Construction.p_over_q_le_a_over_b n'' 1 b (r'' : ℤ) (s'' : ℤ)
      (by exact_mod_cast hn''_ge1) (by norm_num) (by exact_mod_cast hb_pos)
      (by positivity) (by positivity)
    rw [hp'_eq, hq'_eq]
    have h_a_eq : Construction.a n'' (1 : ℤ) b (r'' : ℤ) (s'' : ℤ) = (a'' : ℤ) := by
      simp only [Construction.a]
      have hd : b^n'' + b * s'' + r'' = a'' := hdecomp
      push_cast at hd ⊢
      linarith
    rw [h_a_eq] at h
    simpa only [Nat.cast_one, Int.cast_natCast] using h
  -- Step 9: Show p'/q' ≤ p/q (for the lifting lemma)
  have hpq'_le_pq : (p' : ℚ) / q' ≤ (p : ℚ) / q := by
    have ha''_le_bp_q : (a'' : ℚ) / b ≤ (p : ℚ) / q := by
      -- a'' = ⌊b*p/q⌋, so a''/b ≤ (b*p/q)/b = p/q
      have h := Nat.div_mul_le_self (b * p) q
      have h' : a'' * q ≤ b * p := h
      have h'' : (a'' : ℚ) * q ≤ (b : ℚ) * p := by exact_mod_cast h'
      have hq_pos_rat : (0 : ℚ) < q := by exact_mod_cast hq_pos
      have hb_pos_rat : (0 : ℚ) < b := by exact_mod_cast hb_pos
      calc (a'' : ℚ) / b = (a'' : ℚ) * q / (b * q) := by field_simp
        _ ≤ (b : ℚ) * p / (b * q) := by
            apply div_le_div_of_nonneg_right h'' (by positivity)
        _ = (p : ℚ) / q := by field_simp
    calc (p' : ℚ) / q' ≤ (a'' : ℚ) / b := hpq'_le
      _ ≤ (p : ℚ) / q := ha''_le_bp_q
  -- Step 10: Use lifting lemma to get E_{a/b} with a/b = p/q
  haveI hp'_nz : NeZero p' := hp'_ne
  obtain ⟨a, b_out, ha_ne, hb_out_pos, hab_eq, h_lift⟩ :=
    @addSubgroupShannonCapacity_lift p' q' p q hp'_nz hq'_pos hp_ne hq_pos hpq'_le_pq
  use a, b_out, ha_ne, hab_eq
  haveI : NeZero a := ha_ne
  -- b_out ≤ a follows from a/b_out = p/q and p/q > 5 > 1
  have hb_out_le_a : b_out ≤ a := by
    have h5 : (5 : ℝ) ≤ max 5 ((b_for_small_ε : ℝ)^n_needed) := le_max_left _ _
    have hpq_gt_5 : (5 : ℝ) < (p : ℝ) / q := lt_of_le_of_lt h5 hpq_large
    have hpq_gt_1 : (1 : ℝ) < (p : ℝ) / q := by linarith
    have hp_gt_q : q < p := by
      rw [one_lt_div hq_pos_real] at hpq_gt_1
      exact_mod_cast hpq_gt_1
    have hab_rat : (a : ℚ) / b_out = (p : ℚ) / q := hab_eq
    have hb_out_pos_rat : (0 : ℚ) < b_out := by exact_mod_cast hb_out_pos
    have hab_gt_1 : (1 : ℚ) < (a : ℚ) / b_out := by
      rw [hab_rat, one_lt_div (by exact_mod_cast hq_pos : (0 : ℚ) < q)]
      exact_mod_cast hp_gt_q
    rw [one_lt_div hb_out_pos_rat] at hab_gt_1
    exact_mod_cast le_of_lt hab_gt_1
  -- Upper bound on capacity
  have h_upper : addSubgroupShannonCapacity (fractionGraph a b_out) ≤ (a : ℝ) / b_out := by
    calc addSubgroupShannonCapacity (fractionGraph a b_out)
        ≤ shannonCapacity (fractionGraph a b_out) :=
          addSubgroupShannonCapacity_le_shannonCapacity _
      _ ≤ (a : ℝ) / b_out := shannonCapacity_fractionGraph_le a b_out hb_out_pos hb_out_le_a
  -- Since a/b_out = p/q, we have (a : ℝ) / b_out = (p : ℝ) / q
  have hab_real : (a : ℝ) / b_out = (p : ℝ) / q := by
    have : (a : ℚ) / b_out = (p : ℚ) / q := hab_eq
    field_simp at this ⊢
    exact_mod_cast this
  -- Step 11: Lower bound from construction + lifting
  have h_lower :
      addSubgroupShannonCapacity (fractionGraph a b_out) ≥ (p' : ℝ) ^ (1 / (n'' : ℝ)) := by
    calc addSubgroupShannonCapacity (fractionGraph a b_out)
        ≥ addSubgroupShannonCapacity (fractionGraph p' q') := h_lift
      _ ≥ (p' : ℝ) ^ (1 / (n'' : ℝ)) := hconstr
  -- Step 12: Apply delta_bound to show a''/b - (p')^(1/n'') ≤ 6b²/n''
  have hgap_le : (a'' : ℝ) / b - (p' : ℝ) ^ (1 / (n'' : ℝ)) ≤ 6 * (b : ℝ)^2 / n'' := by
    have hdb := delta_bound (n'' : ℝ) 1 (b : ℝ) (r'' : ℝ) (s'' : ℝ)
      (by exact_mod_cast hn''_ge1) (by norm_num) (by exact_mod_cast hb_ge_1)
      (by exact_mod_cast hb_ge_1) (by positivity) (by exact_mod_cast hr''_le)
      (by positivity) (by exact_mod_cast hs''_le)
    -- Need to show the gap = Delta n'' 1 b r'' s''
    have hgap_eq : (a'' : ℝ) / b - (p' : ℝ) ^ (1 / (n'' : ℝ)) =
        Delta (n'' : ℝ) 1 b (r'' : ℝ) (s'' : ℝ) := by
      unfold Delta
      simp only [div_one, one_mul]
      have h_a_eq_a'' : (b : ℝ) ^ (n'' : ℝ) + (s'' : ℝ) * b + (r'' : ℝ) = (a'' : ℝ) := by
        have hd : b^n'' + b * s'' + r'' = a'' := hdecomp
        have hd_cast : ((b^n'' + b * s'' + r'' : ℕ) : ℝ) = (a'' : ℝ) := by exact_mod_cast hd
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hd_cast
        rw [Real.rpow_natCast]; linarith
      have hp'_eq_real : (p' : ℝ) =
          ((r'' : ℝ) * (s'' : ℝ)^(n'' : ℝ) + (a'' : ℝ)^(n'' : ℝ)) /
          ((r'' : ℝ) + (b : ℝ)^(n'' : ℝ)) := by
        have h_a_eq : Construction.a n'' (1 : ℤ) b (r'' : ℤ) (s'' : ℤ) = (a'' : ℤ) := by
          simp only [Construction.a]
          have hd : b^n'' + b * s'' + r'' = a'' := hdecomp
          push_cast at hd ⊢; linarith
        have hp'_rat : (p' : ℚ) = Construction.p n'' 1 b (r'' : ℤ) (s'' : ℤ) := hp'_eq
        simp only [Construction.p] at hp'_rat
        rw [h_a_eq] at hp'_rat
        have hp'_ℝ : (p' : ℝ) = ((p' : ℚ) : ℝ) := by norm_cast
        rw [hp'_ℝ, hp'_rat]
        simp only [Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_pow,
                   Rat.cast_intCast, Rat.cast_natCast, Int.cast_natCast]
        congr 1
        · rw [mul_comm, Real.rpow_natCast, Real.rpow_natCast]; ring
        · rw [Real.rpow_natCast]; ring
      have hp'_eq_real' : (p' : ℝ) =
          ((r'' : ℝ) * (s'' : ℝ)^(n'' : ℝ) +
           ((b : ℝ) ^ (n'' : ℝ) + (s'' : ℝ) * b + r'')^(n'' : ℝ)) /
          ((r'' : ℝ) + (b : ℝ)^(n'' : ℝ)) := by
        rw [← h_a_eq_a''] at hp'_eq_real; exact hp'_eq_real
      rw [← h_a_eq_a'', hp'_eq_real']
    rw [hgap_eq]
    convert hdb using 2
  -- Step 13: Final calculation combining both bounds
  calc (p : ℝ) / q - addSubgroupShannonCapacity (fractionGraph a b_out)
      = (a : ℝ) / b_out - addSubgroupShannonCapacity (fractionGraph a b_out) := by rw [← hab_real]
    _ ≤ (a : ℝ) / b_out - (p' : ℝ) ^ (1 / (n'' : ℝ)) := by linarith [h_lower]
    _ = (p : ℝ) / q - (p' : ℝ) ^ (1 / (n'' : ℝ)) := by rw [hab_real]
    _ = ((p : ℝ) / q - (a'' : ℝ) / b) + ((a'' : ℝ) / b - (p' : ℝ) ^ (1 / (n'' : ℝ))) := by ring
    _ < ε / 2 + (6 * (b : ℝ)^2 / n'') := by linarith [hpq_a''_lt_eps_half, hgap_le]
    _ < ε / 2 + ε / 2 := by linarith [h6b2_n_lt]
    _ = ε := by ring
end GroupTheoreticShannonCapacity.MainProofs
