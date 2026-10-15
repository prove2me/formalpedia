-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_center_series_jet_patching
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:38:54.919751+00:00
-- url     : https://prove2.me/submissions/4cdd502c-d70c-463d-bdfe-69860e76c832
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_center_box_jet_interpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {iota : Type} [DecidableEq iota] {m : Nat}
    (active : Finset iota)
    (center : iota -> Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) -> Exists fun k => Not (center i k = center j k))
    (S : iota -> MvPowerSeries (Fin (m + 1)) Complex)
    (Q : iota -> MvPolynomial (Fin (m + 1)) Complex)
    (hmatch : (i : iota) -> i ∈ active ->
      (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e k <= degree k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet (center i) (Q i)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S i)) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (i : iota) -> i ∈ active ->
        (e : Fin (m + 1) -> Nat) ->
          ((k : Fin (m + 1)) -> e k <= degree k) ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet (center i) P) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S i) := by
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_jet_interpolation
      active center degree hcenters
      (fun i e => MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S i))
  exact ⟨P, by
    intro i hi e he
    exact hP i hi e he⟩