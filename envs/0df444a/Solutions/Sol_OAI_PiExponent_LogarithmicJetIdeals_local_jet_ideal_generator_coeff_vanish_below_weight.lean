-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_weight
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T11:07:07.508771+00:00
-- url     : https://prove2.me/submissions/1ff81192-28a7-4aca-9e78-d63575728f50
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_coeff_vanish_below_weight_linear
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_mvPowerSeries_coeff_pow_vanish_below_weight

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (n : ℕ) (b : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0) :
    ∀ i : Fin m,
      (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) <
        (n : ℝ) * InterpolationMatrix.rowWeights v0 theta w i.succ →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (AdmissibleFormalInterpolation.formalJet c
          (jetCoordinate c T i.succ ^ n)) = 0 := by
  intro i hb
  have hq : ∀ j : Fin (m + 1), 0 < InterpolationMatrix.rowWeights v0 theta w j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hv0
    · simpa [InterpolationMatrix.rowWeights] using div_pos (hw k) htheta
  have hlin :
      ∀ a : Fin (m + 1) → ℕ,
        (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (a j : ℝ)) <
          InterpolationMatrix.rowWeights v0 theta w i.succ →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (AdmissibleFormalInterpolation.formalJet c
            (jetCoordinate c T i.succ)) = 0 := by
    intro a ha
    exact
      OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_weight_linear
        v0 theta w c T a hv0 htheta hw hT i ha
  have hp :=
    OAI.PiExponent.LogarithmicJetIdeals.mvPowerSeries_coeff_pow_vanish_below_weight
      (q := InterpolationMatrix.rowWeights v0 theta w)
      (rho := InterpolationMatrix.rowWeights v0 theta w i.succ)
      (f := AdmissibleFormalInterpolation.formalJet c (jetCoordinate c T i.succ))
      (n := n) hq hlin b hb
  simpa [InterpolationMatrix.exponentVector] using hp