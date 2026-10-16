-- Prove2me | solution 1 for GroverWiki.iterationCount_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T12:57:48.542836+00:00
-- url     : https://prove2.me/submissions/ee3a0854-ac63-4733-aa9c-8e1ffacc8621

import Mathlib
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (hN : 1 ≤ N) :
    ⌊Real.pi / (4 * Real.arcsin (1 / Real.sqrt N))⌋₊ ≤ ⌈Real.pi / 4 * Real.sqrt N⌉₊ := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]
  have hx : 0 < 1 / Real.sqrt (N : ℝ) := by positivity
  have hx1 : 1 / Real.sqrt (N : ℝ) ≤ 1 := (div_le_one hs).2 hs1
  have ha0 : 0 ≤ Real.arcsin (1 / Real.sqrt (N : ℝ)) :=
    Real.arcsin_nonneg.2 hx.le
  have hsin := Real.sin_le ha0
  rw [Real.sin_arcsin (by linarith : -(1 : ℝ) ≤ 1 / Real.sqrt (N : ℝ)) hx1] at hsin
  have ha : 0 < Real.arcsin (1 / Real.sqrt (N : ℝ)) := lt_of_lt_of_le hx hsin
  have hbound : Real.pi / (4 * Real.arcsin (1 / Real.sqrt (N : ℝ))) ≤
      Real.pi / 4 * Real.sqrt N := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.arcsin (1 / Real.sqrt (N : ℝ)))).2
    have hinv : (1 / Real.sqrt (N : ℝ)) * Real.sqrt N = 1 := by
      field_simp
    have hm := mul_le_mul_of_nonneg_right hsin hs.le
    rw [hinv] at hm
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.2 hm)]
  have hfloor := Nat.floor_le (by positivity :
      0 ≤ Real.pi / (4 * Real.arcsin (1 / Real.sqrt (N : ℝ))))
  have hceil := Nat.le_ceil (Real.pi / 4 * Real.sqrt (N : ℝ))
  exact_mod_cast le_trans hfloor (le_trans hbound hceil)
