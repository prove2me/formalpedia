-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.localJetIdeals_pairwise_comaximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T21:09:35.322986+00:00
-- url     : https://prove2.me/submissions/cb8bd5da-fe40-432b-b73e-0fdee4b09562

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeals_comaximal_of_ne
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_scaled_centers_ne_of_injective

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i)) :
    ∀ j k : Fin K, j ≠ k →
      localJetIdeal (fun i => (j.val : ℂ) * r i) T e ⊔
        localJetIdeal (fun i => (k.val : ℂ) * r i) T e = ⊤ := by
  intro j k hjk
  apply OAI.PiExponent.LogarithmicJetIdeals.localJetIdeals_comaximal_of_ne
  exact OAI.PiExponent.LogarithmicJetIdeals.scaled_centers_ne_of_injective
    K r hc hjk