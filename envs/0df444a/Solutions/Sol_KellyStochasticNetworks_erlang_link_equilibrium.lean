-- Prove2me | solution 1 for KellyStochasticNetworks.erlang_link_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T19:59:45.344962+00:00
-- url     : https://prove2.me/submissions/643fd53e-afea-4f13-a1c5-e25a9ea24187

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang

open KellyStochasticNetworks

theorem solution (lam mu : ℝ) (C : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (π : Fin (C + 1) → ℝ) (h : DetailedBalance π (erlangRates lam mu C)) (j : Fin (C + 1)) :
    π j = (lam / mu) ^ (j : ℕ) / (Nat.factorial (j : ℕ) : ℝ) * π 0 := by
  -- Two-term recursion from detailed balance between neighbouring states `n` and `n + 1`.
  have step : ∀ (n : ℕ) (hn : n + 1 < C + 1),
      π ⟨n + 1, hn⟩ * (((n + 1 : ℕ) : ℝ) * mu) = π ⟨n, by omega⟩ * lam := by
    intro n hn
    have hdb := h ⟨n, by omega⟩ ⟨n + 1, hn⟩
    have h1 : erlangRates lam mu C ⟨n, by omega⟩ ⟨n + 1, hn⟩ = lam := by
      simp [erlangRates]
    have h2 : erlangRates lam mu C ⟨n + 1, hn⟩ ⟨n, by omega⟩ = ((n + 1 : ℕ) : ℝ) * mu := by
      simp [erlangRates]; omega
    rw [h1, h2] at hdb
    linarith
  have key : ∀ (n : ℕ) (hn : n < C + 1),
      π ⟨n, hn⟩ = (lam / mu) ^ n / (Nat.factorial n : ℝ) * π 0 := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
      intro hn
      have hs := step n hn
      have ih' := ih (by omega)
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * mu := by positivity
      have hπ : π ⟨n + 1, hn⟩ = π ⟨n, by omega⟩ * lam / (((n + 1 : ℕ) : ℝ) * mu) := by
        rw [eq_div_iff hpos.ne']; exact hs
      rw [hπ, ih', Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
  exact key j.1 j.2
