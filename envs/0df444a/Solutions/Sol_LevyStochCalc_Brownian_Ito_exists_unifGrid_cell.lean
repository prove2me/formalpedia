-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_unifGrid_cell
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:36:58.449161+00:00
-- url     : https://prove2.me/submissions/c2a29076-5245-448e-a636-402a32b6a9e1

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F000
open LevyStochCalc.Brownian.Ito
theorem solution {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) {s : ℝ}
    (hs : 0 < s) (hsT : s ≤ T) :
    ∃ i : ℕ, i < m ∧ unifGrid T m i < s ∧ s ≤ unifGrid T m (i + 1) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  let r : ℝ := s * m / T
  have hr : 0 < r := by dsimp [r]; positivity
  have hrm : r ≤ m := by dsimp [r]; rw [div_le_iff₀ hT]; nlinarith
  have hc : 0 < ⌈r⌉₊ := Nat.ceil_pos.mpr hr
  have hcm : ⌈r⌉₊ ≤ m := Nat.ceil_le.mpr hrm
  refine ⟨⌈r⌉₊-1, by omega, ?_⟩
  have he : (⌈r⌉₊-1)+1 = ⌈r⌉₊ := by omega
  have hceil : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
  have hlt : ((⌈r⌉₊-1 : ℕ) : ℝ) < r := by
    apply Nat.lt_ceil.mp
    omega
  unfold unifGrid
  constructor
  · rw [div_lt_iff₀ hm]
    have hh := (lt_div_iff₀ hT).mp hlt
    dsimp [r] at hh
    nlinarith
  · rw [he, le_div_iff₀ hm]
    have hh := (div_le_iff₀ hT).mp hceil
    dsimp [r] at hh
    nlinarith
#print axioms solution
