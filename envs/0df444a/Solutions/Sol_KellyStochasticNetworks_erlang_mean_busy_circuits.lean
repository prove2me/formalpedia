-- Prove2me | solution 1 for KellyStochasticNetworks.erlang_mean_busy_circuits
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T19:57:51.422533+00:00
-- url     : https://prove2.me/submissions/14d9cbf9-464a-4ca1-b2de-038ba7acd385

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang
import Theorems.Thm_KellyStochasticNetworks_erlang_link_equilibrium

open KellyStochasticNetworks

theorem solution (lam mu : ℝ) (C : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (π : Fin (C + 1) → ℝ) (h : DetailedBalance π (erlangRates lam mu C))
    (hsum : ∑ j, π j = 1) :
    ∑ j : Fin (C + 1), ((j : ℕ) : ℝ) * π j
      = (lam / mu) * (1 - erlang (lam / mu) C) := by
  set ν := lam / mu with hν
  set a : ℕ → ℝ := fun j => ν ^ j / (Nat.factorial j : ℝ) with ha
  set Z := ∑ j ∈ Finset.range (C + 1), a j with hZ
  -- Every weight is `ν ^ j / j! * π 0` (milestone `erlang_link_equilibrium`).
  have hπ := erlang_link_equilibrium lam mu C hlam hmu π h
  have hnorm : Z * π 0 = 1 := by
    rw [← hsum, hZ, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range (fun j => a j * π 0)]
    exact Finset.sum_congr rfl (fun j _ => (hπ j).symm)
  have hZpos : 0 < Z := by
    rw [hZ]
    exact Finset.sum_pos (fun j _ => by positivity) ⟨0, by simp⟩
  -- Key identity: `j * a j = ν * a (j - 1)`, so `∑ j * a j = ν * (Z - a C)`.
  have hshift : ∑ j ∈ Finset.range (C + 1), (j : ℝ) * a j = ν * (Z - a C) := by
    rw [Finset.sum_range_succ', hZ, Finset.sum_range_succ, add_sub_cancel_right,
      Finset.mul_sum]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ha, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
  have hlhs : ∑ j : Fin (C + 1), ((j : ℕ) : ℝ) * π j
      = (∑ j ∈ Finset.range (C + 1), (j : ℝ) * a j) * π 0 := by
    rw [Finset.sum_mul, ← Fin.sum_univ_eq_sum_range (fun j => (j : ℝ) * a j * π 0)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hπ j]; ring
  have hπ0 : π 0 = 1 / Z := by
    rw [eq_div_iff hZpos.ne']; linarith
  rw [hlhs, hshift, hπ0, erlang, ← hZ]
  field_simp
  simp only [ha]
  field_simp
