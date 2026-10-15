-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_scale_first_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T10:05:17.834231+00:00
-- url     : https://prove2.me/submissions/da79c756-8836-4892-8a3a-f892eb9e2fc4

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_first_coordinate_weight_bound
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_first_coordinate_power_coeff_vanish

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
    (b : Fin (m + 1) → ℕ)
    (hb : (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) < R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.formalJet c
        (jetCoordinate c T (0 : Fin (m + 1)) ^ e (0 : Fin (m + 1))) ) = 0 := by
  have hdegree : b (0 : Fin (m + 1)) < e (0 : Fin (m + 1)) :=
    OAI.PiExponent.LogarithmicJetIdeals.first_coordinate_weight_bound
      v0 theta w R e hv0 htheta hw he b hb
  exact OAI.PiExponent.LogarithmicJetIdeals.formalJet_first_coordinate_power_coeff_vanish
    c T b (e (0 : Fin (m + 1))) hdegree