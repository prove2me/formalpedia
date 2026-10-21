-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_jet_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:49:24.014773+00:00
-- url     : https://prove2.me/submissions/e25f21d5-b8f4-40a1-a21e-5e3f94236deb

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_center_box_plain_jet_interpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_box_change_of_coordinates

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {iota : Type} [DecidableEq iota] {m : Nat}
    (active : Finset iota)
    (center : iota -> Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) -> Exists fun k => Not (center i k = center j k))
    (value : iota -> (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (i : iota) -> i ∈ active ->
        (e : Fin (m + 1) -> Nat) ->
          ((k : Fin (m + 1)) -> e k <= degree k) ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet (center i) P) = value i e := by
  let cutoff : Nat := ∑ k : Fin (m + 1), degree k
  obtain ⟨standardValue, hchange⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_box_change_of_coordinates
      active center degree value
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_plain_jet_interpolation
      active center (fun _ => cutoff) hcenters standardValue
  exact ⟨P, hchange P hP⟩
