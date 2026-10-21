-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_coeff_vanish_below_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T00:16:51.729879+00:00
-- url     : https://prove2.me/submissions/2c25bcab-171a-4f4b-b07c-b085227cdb29

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_coeff_vanish_below_scale
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_coeff_vanish_from_generators

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : Q ∈ localJetIdeal c T e)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet c Q) = 0 := by
  apply OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_coeff_vanish_from_generators
      v0 theta w c R T e
  · intro j
    simpa [InterpolationMatrix.rowWeights] using
      (Fin.cases hv0 (fun i => div_pos (hw i) htheta) j)
  · intro b hb i
    exact OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_scale
      v0 theta w c R T e hv0 htheta hw hR he hT b hb i
  · exact hQ
  · exact ha