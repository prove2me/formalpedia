-- Prove2me | solution 1 for IntMul.Kappa.kappaBound_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T19:41:08.931621+00:00
-- url     : https://prove2.me/submissions/f68b07cc-c6e9-417f-8d40-f6be72d09818

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_IntMul_Kappa_mul_time_bound_of_eventual_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open IntMul

theorem solution {κ κ' : ℝ}
    (hκ : κ ≤ κ') (hstrong : KappaBound κ') :
    KappaBound κ := by
  change MulTimeBound (fun n : ℕ =>
    (n : ℝ) * ((lg n : ℝ) ^ (1 - κ)))
  change MulTimeBound (fun n : ℕ =>
    (n : ℝ) * ((lg n : ℝ) ^ (1 - κ'))) at hstrong
  apply IntMul.Kappa.mul_time_bound_of_eventual_le
    (g := fun n : ℕ => (n : ℝ) * ((lg n : ℝ) ^ (1 - κ')))
    (h := fun n : ℕ => (n : ℝ) * ((lg n : ℝ) ^ (1 - κ)))
  · refine ⟨0, ?_⟩
    intro n hn hn1
    have hlg_nat : 1 ≤ lg n := by
      exact le_max_right (Nat.clog 2 n) 1
    have hlg : (1 : ℝ) ≤ (lg n : ℝ) := by
      exact_mod_cast hlg_nat
    have hrpow : ((lg n : ℝ) ^ (1 - κ')) ≤
        ((lg n : ℝ) ^ (1 - κ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hlg
      linarith
    exact mul_le_mul_of_nonneg_left hrpow (Nat.cast_nonneg n)
  · exact hstrong
