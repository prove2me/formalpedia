-- Prove2me | solution 1 for MassEnergyEquivalence.relEnergy_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T08:19:16.075975+00:00
-- url     : https://prove2.me/submissions/a4fb1c75-522d-4e55-9013-42a7aad34d95

import Mathlib
import Definitions.Def_MassEnergyEquivalence_Defs
import Theorems.Thm_AppliedComb_GenFun_central_binom_genfun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- Central-binomial generating functions give the subluminal Lorentz energy series. -/
theorem solution (c m : ℝ) (v : Vec3) (hc : 0 < c) (hm : 0 ≤ m)
    (hv : ‖v‖ < c) :
    HasSum (fun n : ℕ =>
      m * c ^ 2 * ((Nat.centralBinom n : ℝ) / 4 ^ n) *
        (‖v‖ / c) ^ (2 * n)) (relEnergy c m v) := by
  let a : ℝ := ‖v‖ / c
  let z : ℝ := a ^ 2 / 4
  have ha0 : 0 ≤ a := div_nonneg (norm_nonneg _) (le_of_lt hc)
  have ha1 : a < 1 := by
    dsimp [a]
    exact (div_lt_iff₀ hc).2 (by simpa only [one_mul] using hv)
  have ha2 : a ^ 2 < 1 := by nlinarith [mul_pos (sub_pos.mpr ha1) (add_pos_of_pos_of_nonneg (by norm_num : (0:ℝ)<1) ha0)]
  have hz0 : 0 ≤ z := div_nonneg (sq_nonneg _) (by norm_num)
  have hz : |z| < 1 / 4 := by
    rw [abs_of_nonneg hz0]
    dsimp [z]
    nlinarith
  have hpositive : 0 < 1 - 4 * z := by
    dsimp [z]
    nlinarith [ha2]
  have hargument : 1 - 4 * z = 1 - ‖v‖ ^ 2 / c ^ 2 := by
    dsimp [z, a]
    rw [div_pow]
    ring
  have hpower :
      (1 - 4 * z) ^ (-(1 / 2 : ℝ)) =
        1 / Real.sqrt (1 - 4 * z) := by
    simp only [Real.sqrt_eq_rpow, one_div,
      Real.rpow_neg (le_of_lt hpositive)]
  have hseries :=
    (AppliedComb.GenFun.central_binom_genfun z hz).mul_left (m * c ^ 2)
  have hterms :
      (fun n : ℕ => m * c ^ 2 * ((Nat.centralBinom n : ℝ) / 4 ^ n) *
        (‖v‖ / c) ^ (2 * n)) =
      (fun n : ℕ => (m * c ^ 2) *
        ((Nat.choose (2 * n) n : ℝ) * z ^ n)) := by
    funext n
    dsimp [z, a]
    simp only [Nat.centralBinom, div_pow, pow_mul]
    ring
  have hvalue :
      m * c ^ 2 * (1 - 4 * z) ^ (-(1 / 2 : ℝ)) =
        relEnergy c m v := by
    rw [hpower, hargument]
    unfold relEnergy lorentzFactor
    ring
  rw [hterms, ← hvalue]
  exact hseries
