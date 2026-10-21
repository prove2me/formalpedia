-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.ideal_power_packet_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T18:12:11.470406+00:00
-- url     : https://prove2.me/submissions/f0d09e85-cf0a-4520-b31c-8d30b99d62ee

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_simultaneous_jet_ideal_coeff_vanish_below_scale
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_ideal_power_raw_packet_of_coefficient_profile

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (r : Fin m → ℂ)
    (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (he : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (simultaneousJetIdeal K r T e) ^ n) :
    rawPacketMap K v0 theta w ((n : ℝ) * R) r P = 0 := by
  have hweights : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i := by
    intro i
    cases i using Fin.cases with
    | zero => simpa [InterpolationMatrix.rowWeights] using hv0
    | succ j => exact div_pos (hw j) htheta
  have hcoeff : ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ),
      Q ∈ simultaneousJetIdeal K r T e →
      ∀ (j : Fin K) (a : Fin (m + 1) → ℕ),
        (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (AdmissibleFormalInterpolation.formalJet
            (fun i => (j.val : ℂ) * r i) Q) = 0 := by
    intro Q hQ j a ha
    exact simultaneous_jet_ideal_coeff_vanish_below_scale
      K v0 theta w r R T e hv0 htheta hw hR he hT Q hQ j a ha
  exact ideal_power_raw_packet_of_coefficient_profile K v0 theta w r R n
    hweights (simultaneousJetIdeal K r T e) hcoeff P hP
