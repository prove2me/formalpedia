-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.q_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:37.898514+00:00
-- url     : https://prove2.me/submissions/fcfb3121-4a02-4caf-a6d9-fc513e695c74

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) [NeZero n] (k b r s : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    (0 : ℝ) < (q n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) := by
  have ha_pos : (0 : ℚ) < (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℚ) := by simp only [a]; positivity
  have hk_pos : (0 : ℚ) < (k : ℚ) := by positivity
  have hb_pos : (0 : ℚ) < (b : ℚ) := by positivity
  have hbn_pos : (0 : ℚ) < (b : ℚ)^n := pow_pos hb_pos n
  have hr_nonneg : (0 : ℚ) ≤ (r : ℚ) := by positivity
  have ha_pow_pos : (0 : ℚ) < (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℚ)^(n-1) := pow_pos ha_pos _
  have hd_pos : (0 : ℚ) < (r : ℚ) + (k : ℚ) * (b : ℚ)^n := by
    linarith [mul_pos hk_pos hbn_pos]
  have hnum_pos : (0 : ℚ) < (s : ℚ)^(n-1) * r + k * b * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ))^(n-1) := by
    have term2_pos : (0 : ℚ) < (k : ℚ) * b * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℚ)^(n-1) :=
      mul_pos (mul_pos hk_pos hb_pos) ha_pow_pos
    have term1_nonneg : (0 : ℚ) ≤ (s : ℚ)^(n-1) * r := by positivity
    linarith
  simp only [q]
  have h_q_pos : (0 : ℚ) < (s^(n-1) * r + k * b * (a n k b r s)^(n-1)) / (r + k * b^n) :=
    div_pos hnum_pos hd_pos
  exact_mod_cast h_q_pos
end GroupTheoreticShannonCapacity.Construction
