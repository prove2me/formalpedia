-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_polynomialJet_eq_zero_of_mem_localJetIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:06:38.956341+00:00
-- url     : https://prove2.me/submissions/9c3fd828-be71-4f50-8b46-ee6a415f2255

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomialJet_mem_coordinatePowerIdeal
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_eq_zero_of_mem_coordinatePowerIdeal

open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ localJetIdeal c T b)
    (u : Fin (m + 1) →₀ ℕ) (hu : ∀ i, u i < b i) :
    MvPolynomial.coeff u (polynomialJet c T P) = 0 := by
  have hQ := OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_mem_coordinatePowerIdeal
    c T b P hP
  exact OAI.PiExponent.LogarithmicJetIdeals.coeff_eq_zero_of_mem_coordinatePowerIdeal
    b (polynomialJet c T P) hQ u hu