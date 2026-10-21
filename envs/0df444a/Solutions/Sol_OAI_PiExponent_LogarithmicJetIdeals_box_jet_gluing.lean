-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.box_jet_gluing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:25:55.460545+00:00
-- url     : https://prove2.me/submissions/b2c3299f-b580-4381-9a5b-2e755133671c

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_box_series_jet_interpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {iota alpha : Type} [Fintype alpha] [DecidableEq alpha] {m : Nat}
    (center : iota -> Fin m -> Complex) (slot : alpha -> iota)
    (degree : alpha -> Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) -> Exists fun k => Not (center i k = center j k))
    (Q : iota -> MvPolynomial (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (b : alpha) -> (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> LE.le (e k) (degree b k)) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet (center (slot b)) P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet (center (slot b)) (Q (slot b))) := by
  exact OAI.PiExponent.LogarithmicJetIdeals.finite_box_series_jet_interpolation
    center slot degree hcenters (fun i => formalJet (center i) (Q i))