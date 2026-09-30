-- Prove2me | solution 1 for KellyStochasticNetworks.reversible_iff_detailed_balance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T19:59:48.09225+00:00
-- url     : https://prove2.me/submissions/0b6f5946-03a3-4733-99ed-48209e327a1a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

open KellyStochasticNetworks

theorem solution {S : Type*} (π : S → ℝ) (q : S → S → ℝ)
    (hπ : ∀ j, 0 < π j) : reversedRates π q = q ↔ DetailedBalance π q := by
  constructor
  · intro hq j k
    have hjk := congrFun (congrFun hq j) k
    simp only [reversedRates] at hjk
    rw [div_eq_iff (hπ j).ne'] at hjk
    linarith
  · intro hdb
    funext j k
    simp only [reversedRates]
    rw [div_eq_iff (hπ j).ne', ← hdb j k]
    ring
