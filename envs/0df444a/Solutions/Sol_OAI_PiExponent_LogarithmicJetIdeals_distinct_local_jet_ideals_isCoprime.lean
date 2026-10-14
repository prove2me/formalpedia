-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.distinct_local_jet_ideals_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T23:52:49.470808+00:00
-- url     : https://prove2.me/submissions/bb7bdd11-698f-4065-897d-5cd65f04babb

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeal_isCoprime_of_ne

open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i)) :
    ∀ j k : Fin K, j ≠ k →
      IsCoprime
        (localJetIdeal (fun i => (j.val : ℂ) * r i) T e)
        (localJetIdeal (fun i => (k.val : ℂ) * r i) T e) := by
  intro j k hjk
  apply localJetIdeal_isCoprime_of_ne
  intro hcenters
  exact hjk (hc hcenters)