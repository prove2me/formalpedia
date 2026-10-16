-- Prove2me | solution 1 for GroverWiki.groverMatrix_success_amplitude_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:37:25.695524+00:00
-- url     : https://prove2.me/submissions/043cc73a-a622-4078-a693-0b18a92388a7

import Mathlib
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open GroverWiki

theorem solution (r : ℕ) :
    ‖![(1 : ℂ), 1 / (Real.sqrt ((1 : ℕ) : ℝ) : ℂ)] ⬝ᵥ
        ((!![1, 2 / (Real.sqrt ((1 : ℕ) : ℝ) : ℂ);
          -2 / (Real.sqrt ((1 : ℕ) : ℝ) : ℂ),
          1 - 4 / (((1 : ℕ)) : ℂ)] ^ r) *ᵥ
          ![0, 1])‖ ^ 2 =
      Real.sin ((2 * r + 1) * Real.arcsin (1 / Real.sqrt (((1 : ℕ)) : ℝ))) ^ 2 := by
  classical
  let M : Matrix (Fin 2) (Fin 2) ℂ :=
    !![1, 2 / (Real.sqrt ((1 : ℕ) : ℝ) : ℂ);
      -2 / (Real.sqrt ((1 : ℕ) : ℝ) : ℂ),
      1 - 4 / (((1 : ℕ)) : ℂ)]
  let q : Fin 2 → ℂ := ![(1 : ℂ), 1 / (Real.sqrt ((1 : ℕ) : ℝ) : ℂ)]
  let e : Fin 2 → ℂ := ![0, 1]
  have hrow (v : Fin 2 → ℂ) : q ⬝ᵥ (M *ᵥ v) = -(q ⬝ᵥ v) := by
    simp [q, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hamp (k : ℕ) : q ⬝ᵥ (M ^ k *ᵥ e) = (-1 : ℂ) ^ k := by
    induction k with
    | zero => simp [q, e]
    | succ k ih =>
      have hk : M ^ (k + 1) *ᵥ e = M *ᵥ (M ^ k *ᵥ e) := by
        calc
          M ^ (k + 1) *ᵥ e = (M * M ^ k) *ᵥ e := by rw [pow_succ']
          _ = M *ᵥ (M ^ k *ᵥ e) := by rw [Matrix.mulVec_mulVec]
      rw [hk, hrow, ih]
      simp [pow_succ]
  have htrig : Real.sin ((2 * r + 1) * Real.arcsin (1 : ℝ)) ^ 2 = 1 := by
    have hangle : (2 * (r : ℝ) + 1) * Real.arcsin (1 : ℝ) = (2 * (r : ℝ) + 1) * (Real.pi / 2) := by
      rw [Real.arcsin_one]
    have harg : (2 * (r : ℝ) + 1) * (Real.pi / 2) = (r : ℝ) * Real.pi + Real.pi / 2 := by ring
    have hr : ((-1 : ℝ) ^ r) ^ 2 = 1 := by
      calc
        ((-1 : ℝ) ^ r) ^ 2 = (-1 : ℝ) ^ (r * 2) := by rw [← pow_mul]
        _ = (-1 : ℝ) ^ (2 * r) := by rw [Nat.mul_comm]
        _ = ((-1 : ℝ) ^ 2) ^ r := by rw [pow_mul]
        _ = 1 := by norm_num
    rw [hangle, harg, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
    exact hr
  have hq : ‖q ⬝ᵥ (M ^ r *ᵥ e)‖ ^ 2 = 1 := by
    rw [hamp]
    simp
  have htrigN : Real.sin ((2 * r + 1) * Real.arcsin (1 / Real.sqrt (((1 : ℕ)) : ℝ))) ^ 2 = 1 := by
    simpa [Real.sqrt_one, Nat.cast_one] using htrig
  have hfinal : ‖q ⬝ᵥ (M ^ r *ᵥ e)‖ ^ 2 =
      Real.sin ((2 * r + 1) * Real.arcsin (1 / Real.sqrt (((1 : ℕ)) : ℝ))) ^ 2 :=
    hq.trans htrigN.symm
  simpa [q, M, e, Real.sqrt_one, Nat.cast_one] using hfinal
