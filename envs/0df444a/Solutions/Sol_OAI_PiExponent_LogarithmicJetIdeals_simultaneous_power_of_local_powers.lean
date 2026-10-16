-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.simultaneous_power_of_local_powers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T21:05:43.239932+00:00
-- url     : https://prove2.me/submissions/e9907ba1-d57e-48db-af12-72574999849f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeals_pairwise_comaximal
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_iInf_pow_eq_pow_iInf_of_pairwise_sup_eq_top

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hlocal : ∀ j : Fin K,
      P ∈ localJetIdeal (fun i => (j.val : ℂ) * r i) T e ^ n) :
    P ∈ (simultaneousJetIdeal K r T e) ^ n := by
  have hpair : ∀ j k : Fin K, j ≠ k →
      localJetIdeal (fun i => (j.val : ℂ) * r i) T e ⊔
        localJetIdeal (fun i => (k.val : ℂ) * r i) T e = ⊤ := by
    intro j k hjk
    exact OAI.PiExponent.LogarithmicJetIdeals.localJetIdeals_pairwise_comaximal
      K r T e hc j k hjk
  change P ∈ (⨅ j : Fin K,
    localJetIdeal (fun i => (j.val : ℂ) * r i) T e) ^ n
  rw [← OAI.PiExponent.LogarithmicJetIdeals.iInf_pow_eq_pow_iInf_of_pairwise_sup_eq_top
    K (fun j => localJetIdeal (fun i => (j.val : ℂ) * r i) T e) n hpair]
  exact (Ideal.mem_iInf).2 hlocal