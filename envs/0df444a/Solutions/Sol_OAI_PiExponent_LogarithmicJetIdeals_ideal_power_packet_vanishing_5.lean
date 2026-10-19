-- Prove2me | solution 5 for OAI.PiExponent.LogarithmicJetIdeals.ideal_power_packet_vanishing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:31:36.215519+00:00
-- url     : https://prove2.me/submissions/304e4dab-806d-4856-a0f2-d84bce4eac07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_simultaneous_jet_ideal_coeff_vanish_below_scale
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_ideal_power_raw_packet_of_coefficient_profile
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

/-- Apply the proved generic ideal-power coefficient-profile theorem
using the base vanishing estimates for the simultaneous jet ideal. -/
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
    cases i using Fin.cases with
    | zero =>
        simpa [InterpolationMatrix.rowWeights] using hv0
    | succ i =>
        simpa [InterpolationMatrix.rowWeights] using div_pos (hw i) htheta
  have hcoeff :
      ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ),
        Q ∈ simultaneousJetIdeal K r T e →
        ∀ (j : Fin K) (a : Fin (m + 1) → ℕ),
          (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R →
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
            (AdmissibleFormalInterpolation.formalJet
              (fun i => (j.val : ℂ) * r i) Q) = 0 := by
    intro Q hQ j a ha
    exact OAI.PiExponent.LogarithmicJetIdeals.simultaneous_jet_ideal_coeff_vanish_below_scale
      K v0 theta w r R T e hv0 htheta hw hR he hT Q hQ j a ha
  exact OAI.PiExponent.LogarithmicJetIdeals.ideal_power_raw_packet_of_coefficient_profile
    K v0 theta w r R n hv (simultaneousJetIdeal K r T e) hcoeff P hP
