-- Prove2me | solution 1 for LSWCuttingPlane.ChasingZero.union_bound_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:37:27.71058+00:00
-- url     : https://prove2.me/submissions/1bf59bb2-446e-4c4d-8c79-b9f7fd6439c0

import Mathlib
import Definitions.Def_LSWCuttingPlane_ChasingZero_Setting

set_option autoImplicit false

theorem solution (m : ℕ) (hm : 0 < m) (p : ℝ) (hp : 0 < p) :
    let lam : ℕ → ℝ := fun k => 4 * (m : ℝ) * ((k : ℝ) + 1) ^ 2 / p
    Summable (fun k : ℕ => 2 * (m : ℝ) / lam k) ∧
      Summable (fun k : ℕ => p / (2 * ((k : ℝ) + 1) ^ 2)) ∧
      1 - ∑' k : ℕ, 2 * (m : ℝ) / lam k = 1 - ∑' k : ℕ, p / (2 * ((k : ℝ) + 1) ^ 2) ∧
      1 - p ≤ 1 - ∑' k : ℕ, p / (2 * ((k : ℝ) + 1) ^ 2) := by
  intro lam
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlam : ∀ k : ℕ, 2 * (m : ℝ) / lam k = p / (2 * ((k : ℝ) + 1) ^ 2) := by
    intro k
    have hk : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
    simp only [lam]
    field_simp <;> ring
  have hfun : (fun k : ℕ => 2 * (m : ℝ) / lam k) = fun k : ℕ => p / (2 * ((k : ℝ) + 1) ^ 2) :=
    funext hlam
  have hz : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hz' : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 hz
    simpa using this
  have hs : HasSum (fun k : ℕ => p / (2 * ((k : ℝ) + 1) ^ 2)) (p / 2 * (Real.pi ^ 2 / 6)) := by
    have e : (fun k : ℕ => p / (2 * ((k : ℝ) + 1) ^ 2)) =
        fun k : ℕ => p / 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
      funext k
      have hk : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
      field_simp
    rw [e]
    exact hz'.mul_left (p / 2)
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  have hbound : ∑' k : ℕ, p / (2 * ((k : ℝ) + 1) ^ 2) ≤ p := by
    rw [hs.tsum_eq]
    nlinarith
  refine ⟨?_, hs.summable, ?_, ?_⟩
  · rw [hfun]; exact hs.summable
  · rw [hfun]
  · linarith
