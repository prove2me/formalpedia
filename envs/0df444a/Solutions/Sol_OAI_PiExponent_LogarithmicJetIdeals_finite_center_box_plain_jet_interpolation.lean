-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_plain_jet_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:59:19.638729+00:00
-- url     : https://prove2.me/submissions/744cbfb4-bb56-4d6f-b945-9a1fab048a70

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plain_jet_box_local_realization
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plain_jet_box_congruence
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_center_box_ideal_CRT

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {iota : Type} [DecidableEq iota] {m : Nat}
    (active : Finset iota)
    (center : iota -> Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) ->
      Exists fun k => Not (center i k = center j k))
    (value : iota -> (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (i : iota) -> i ∈ active ->
        (e : Fin (m + 1) -> Nat) ->
          ((k : Fin (m + 1)) -> e k <= degree k) ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) P) = value i e := by
  classical
  let localPoly : iota -> MvPolynomial (Fin (m + 1)) Complex := fun i =>
    Classical.choose
      (OAI.PiExponent.LogarithmicJetIdeals.plain_jet_box_local_realization
        (center i) degree (value i))
  have hlocal : (i : iota) -> (e : Fin (m + 1) -> Nat) ->
      ((k : Fin (m + 1)) -> e k <= degree k) ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) (localPoly i)) = value i e := by
    intro i e he
    exact Classical.choose_spec
      (OAI.PiExponent.LogarithmicJetIdeals.plain_jet_box_local_realization
        (center i) degree (value i)) e he
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_ideal_CRT
      active center degree hcenters localPoly
  refine ⟨P, fun i hi e he => ?_⟩
  calc
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) P) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) (localPoly i)) :=
      OAI.PiExponent.LogarithmicJetIdeals.plain_jet_box_congruence
        (center i) degree P (localPoly i) (hP i hi) e he
    _ = value i e := hlocal i e he