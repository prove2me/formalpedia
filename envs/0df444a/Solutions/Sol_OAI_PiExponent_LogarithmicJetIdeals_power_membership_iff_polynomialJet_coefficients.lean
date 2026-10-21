-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.power_membership_iff_polynomialJet_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:16:47.168045+00:00
-- url     : https://prove2.me/submissions/b6dbc7d7-ba58-4fda-a5b4-fba6726465f1

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.Ideal.Lattice
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeal_power_membership_iff_polynomialJet_coefficients
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_simultaneousJetIdeal_pow_eq_iInf_localJetIdeal_pow

open OAI.PiExponent OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hr : ∃ i, r i ≠ 0) (he : ∀ i, 0 < e i)
    (k : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    P ∈ (simultaneousJetIdeal K r T e) ^ k ↔
      ∀ j : Fin K, ∀ u : Fin (m + 1) →₀ ℕ,
        (∑ i, u i / e i) < k →
          MvPolynomial.coeff u
            (polynomialJet (fun i => (j.val : ℂ) * r i) T P) = 0 := by
  rw [OAI.PiExponent.LogarithmicJetIdeals.simultaneousJetIdeal_pow_eq_iInf_localJetIdeal_pow
    K r T e hr he k]
  rw [Ideal.mem_iInf]
  constructor
  · intro h j u hu
    exact (OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_power_membership_iff_polynomialJet_coefficients
      (fun i => (j.val : ℂ) * r i) T e he k P).mp (h j) u hu
  · intro h j
    apply (OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_power_membership_iff_polynomialJet_coefficients
      (fun i => (j.val : ℂ) * r i) T e he k P).mpr
    intro u hu
    exact h j u hu
