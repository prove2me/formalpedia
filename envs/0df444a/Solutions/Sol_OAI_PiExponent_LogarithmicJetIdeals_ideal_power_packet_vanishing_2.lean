-- Prove2me | solution 2 for OAI.PiExponent.LogarithmicJetIdeals.ideal_power_packet_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T11:33:57.850996+00:00
-- url     : https://prove2.me/submissions/72a9e394-d7c7-4641-bb4a-09649063a889

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_simultaneous_jet_ideal_coeff_vanish_below_scale
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_ideal_power_raw_packet_of_coefficient_profile
import Mathlib.Tactic
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
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
  have hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [InterpolationMatrix.rowWeights] using hv0
    · intro j
      simpa [InterpolationMatrix.rowWeights] using div_pos (hw j) htheta
  apply ideal_power_raw_packet_of_coefficient_profile K v0 theta w r R n hv
    (simultaneousJetIdeal K r T e)
  · intro Q hQ j a ha
    exact simultaneous_jet_ideal_coeff_vanish_below_scale
      K v0 theta w r R T e hv0 htheta hw hR he hT Q hQ j a ha
  · exact hP
