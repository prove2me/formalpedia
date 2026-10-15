-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.single_center_series_jet_interpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:39:47.625059+00:00
-- url     : https://prove2.me/submissions/5702e874-a7a5-4509-a385-5ec47653bf00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_total_degree_series_jet_interpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e k <= degree k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S := by
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.total_degree_series_jet_interpolation
      center (∑ k : Fin (m + 1), degree k) S
  refine ⟨P, fun e he => hP e ?_⟩
  exact Finset.sum_le_sum fun k hk => he k