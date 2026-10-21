-- Prove2me | solution 1 for NetMeterDRE.Profit.proposition_1a_existence
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:02:19.050318+00:00
-- url     : https://prove2.me/submissions/b2112f3d-8f11-4829-9d0c-19e5e9f03487

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE

set_option autoImplicit false
open NetMeterDRE.Profit

theorem solution (N : ℕ) (c : ℝ) (hN : 2 < N) (hc : 0 < c) :
    IsSFE N c (fun _ : Fin N => symSupply N c) := by
  intro n ε p hp S' p' hp'
  have hN' : (2 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∀ x : ℝ, ∑ _i : Fin N, symSupply N c x = (N : ℝ) * symSupply N c x := by
    intro x; simp
  rw [IsClearing, hsum] at hp
  rw [IsClearing] at hp'
  have hup : ∀ i : Fin N, Function.update (fun _ : Fin N => symSupply N c) n S' i p' =
      Function.update (fun _ : Fin N => symSupply N c p') n (S' p') i := by
    intro i
    by_cases h : i = n
    · subst h; simp
    · simp [Function.update_of_ne h]
  simp only [hup] at hp'
  rw [Finset.sum_update_of_mem (Finset.mem_univ n)] at hp'
  have hcard : (Finset.univ \ {n} : Finset (Fin N)).card = N - 1 := by
    simp [Finset.card_sdiff]
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hp'
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at hp'
  set k : ℝ := ((N : ℝ) - 2) / (((N : ℝ) - 1) * (2 * c)) with hk
  have hS : ∀ x, symSupply N c x = k * x := by
    intro x; simp only [symSupply, hk]; ring
  have hkc : 2 * c * ((N : ℝ) - 1) * k = (N : ℝ) - 2 := by
    have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
    rw [hk]; field_simp
  have hkpos : 0 < k := by
    rw [hk]; apply div_pos <;> nlinarith
  rw [hS] at hp hp'
  simp only [Function.update_self, hS] at hp' ⊢
  simp only [genProfit, Function.const] at hp' ⊢
  have hq : S' p' = (N : ℝ) * k * p - ((N : ℝ) - 1) * (k * p') := by linarith
  rw [hq]
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  have hA : 0 ≤ ((N : ℝ) - 1) * k + c * ((N : ℝ) - 1) ^ 2 * k ^ 2 := by positivity
  have key : (k * p * p - c * (k * p) ^ 2) -
      ((N * k * p - (N - 1) * (k * p')) * p' - c * (N * k * p - (N - 1) * (k * p')) ^ 2) =
      (((N : ℝ) - 1) * k + c * ((N : ℝ) - 1) ^ 2 * k ^ 2) * (p' - p) ^ 2 := by
    linear_combination (k * (p ^ 2 - p * p')) * hkc
  nlinarith [mul_nonneg hA (sq_nonneg (p' - p))]
