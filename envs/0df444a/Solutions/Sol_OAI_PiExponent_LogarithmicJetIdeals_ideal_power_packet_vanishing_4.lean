-- Prove2me | solution 4 for OAI.PiExponent.LogarithmicJetIdeals.ideal_power_packet_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T19:18:47.082993+00:00
-- url     : https://prove2.me/submissions/a0e3c5e3-c344-4598-8dc8-f91e963316c4

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_ideal_power_raw_packet_of_coefficient_profile
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_simultaneous_jet_ideal_coeff_vanish_below_scale
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  have hv : ∀ i : Fin (m + 1),
      0 < InterpolationMatrix.rowWeights v0 theta w i := by
    intro i
    cases i using Fin.cases with
    | zero => simpa [InterpolationMatrix.rowWeights] using hv0
    | succ i =>
        simpa [InterpolationMatrix.rowWeights] using (div_pos (hw i) htheta)
  apply ideal_power_raw_packet_of_coefficient_profile
    K v0 theta w r R n hv (simultaneousJetIdeal K r T e)
  · intro Q hQ j a ha
    exact simultaneous_jet_ideal_coeff_vanish_below_scale
      K v0 theta w r R T e hv0 htheta hw hR he hT Q hQ j a ha
  · exact hP
