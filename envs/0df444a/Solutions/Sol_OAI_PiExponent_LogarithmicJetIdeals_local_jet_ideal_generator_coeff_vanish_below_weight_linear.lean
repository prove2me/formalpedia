-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_vanish_below_weight_linear
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T11:49:21.485253+00:00
-- url     : https://prove2.me/submissions/23136ef3-375e-41a4-944a-572f1cb04f95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_coeff_support_succ
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_jet_ideal_generator_support_has_weight
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (b : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0) :
    ∀ i : Fin m,
      (∑ j, InterpolationMatrix.rowWeights v0 theta w j * (b j : ℝ)) <
        InterpolationMatrix.rowWeights v0 theta w i.succ →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (AdmissibleFormalInterpolation.formalJet c
          (jetCoordinate c T i.succ)) = 0 := by
  intro i hweight
  by_contra hcoeff
  have hsupport :=
    OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_coeff_support_succ
      c T b i hcoeff
  have hlower :=
    OAI.PiExponent.LogarithmicJetIdeals.local_jet_ideal_generator_support_has_weight
      v0 theta w T b i hv0 htheta hw hT hsupport
  exact (not_lt_of_ge hlower) hweight