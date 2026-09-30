-- Prove2me | solution 1 for KellyStochasticNetworks.erlang_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T19:57:50.08287+00:00
-- url     : https://prove2.me/submissions/767c4a30-f7c8-4cdc-aa3a-cdb0e9a42c59

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang
import Theorems.Thm_KellyStochasticNetworks_erlang_link_equilibrium

open KellyStochasticNetworks

theorem solution (lam mu : ℝ) (C : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (π : Fin (C + 1) → ℝ) (h : DetailedBalance π (erlangRates lam mu C))
    (hsum : ∑ j, π j = 1) :
    π (Fin.last C) = erlang (lam / mu) C := by
  set ν := lam / mu with hν
  set Z := ∑ j ∈ Finset.range (C + 1), ν ^ j / (Nat.factorial j : ℝ) with hZ
  -- Every weight is `ν ^ j / j! * π 0` (milestone `erlang_link_equilibrium`).
  have hπ := erlang_link_equilibrium lam mu C hlam hmu π h
  -- Normalization gives `π 0 * Z = 1`.
  have hnorm : Z * π 0 = 1 := by
    rw [← hsum, hZ, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range
      (fun j => ν ^ j / (Nat.factorial j : ℝ) * π 0)]
    exact Finset.sum_congr rfl (fun j _ => (hπ j).symm)
  have hZpos : 0 < Z := by
    rw [hZ]
    exact Finset.sum_pos (fun j _ => by positivity) ⟨0, by simp⟩
  have hπ0 : π 0 = 1 / Z := by
    rw [eq_div_iff hZpos.ne']; linarith
  rw [hπ (Fin.last C), hπ0, erlang, ← hZ]
  simp only [Fin.val_last]
  ring
