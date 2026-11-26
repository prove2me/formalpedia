-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ceiling_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:26:41.724802+00:00
-- url     : https://prove2.me/submissions/72fb2003-476f-4440-b35c-78402e59fdc1

import Mathlib
open Set
set_option autoImplicit false

/-- The right grid rounding equals the right endpoint throughout a half-open grid cell. -/
theorem solution (T s : ℝ) (hT : 0 < T) (n k : ℕ) (hn : 0 < n)
    (hs : s ∈ Ioc (T * (k : ℝ) / (n : ℝ)) (T * ((k+1 : ℕ) : ℝ) / (n : ℝ))) :
    Nat.ceil (s * (n : ℝ) / T) = k+1 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h1 := (div_lt_iff₀ hn').mp hs.1
  have h2 := (le_div_iff₀ hn').mp hs.2
  have ha : (k : ℝ) < s * (n : ℝ) / T := by
    apply (lt_div_iff₀ hT).mpr
    simpa only [mul_comm T (k : ℝ)] using h1
  have hb : s * (n : ℝ) / T ≤ ((k+1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ hT).mpr
    simpa only [mul_comm T ((k+1 : ℕ) : ℝ)] using h2
  apply le_antisymm (Nat.ceil_le.mpr hb)
  exact Nat.succ_le_of_lt (Nat.lt_ceil.mpr ha)
