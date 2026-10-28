-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_simultaneous_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T21:01:45.68998+00:00
-- url     : https://prove2.me/submissions/94be60ed-bc5b-4e93-abe2-5b3dd53e84c0

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_formalJet_coeff_zero_implies_local_power
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_simultaneous_power_of_local_powers

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (S : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hS : 0 < S)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i ≤ S)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ (j : Fin K) (a : Fin (m + 1) → ℕ),
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        ((n + m : ℕ) : ℝ) * S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet
          (fun i => (j.val : ℂ) * r i) P) = 0) :
    P ∈ (simultaneousJetIdeal K r T e) ^ n := by
  apply OAI.PiExponent.LogarithmicJetIdeals.simultaneous_power_of_local_powers
    (K := K) (r := r) (T := T) (e := e) hc n P
  intro j
  apply OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_local_power
    (v0 := v0) (theta := theta) (w := w) (S := S)
    (c := fun i => (j.val : ℂ) * r i) (T := T) (e := e)
    hS hv he hscale hT n P
  intro a ha
  exact hcoeff j a ha