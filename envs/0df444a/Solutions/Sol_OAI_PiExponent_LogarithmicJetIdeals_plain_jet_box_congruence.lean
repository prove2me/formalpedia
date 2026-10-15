-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.plain_jet_box_congruence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:05:54.862256+00:00
-- url     : https://prove2.me/submissions/acb56075-ae09-4321-9215-293c077d7184
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plain_jet_coeff_zero_of_mem_rectangularJetIdeal

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (c : Fin m -> Complex) (degree : Fin (m + 1) -> Nat)
    (P Q : MvPolynomial (Fin (m + 1)) Complex)
    (h : P - Q ∈ OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal c degree)
    (e : Fin (m + 1) -> Nat)
    (he : (k : Fin (m + 1)) -> e k <= degree k) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c P) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c Q) := by
  have hz := OAI.PiExponent.LogarithmicJetIdeals.plain_jet_coeff_zero_of_mem_rectangularJetIdeal
    c degree (P - Q) h e he
  have hmap : OAI.PiExponent.LogarithmicJetIdeals.plainJet c (P - Q) =
      OAI.PiExponent.LogarithmicJetIdeals.plainJet c P -
        OAI.PiExponent.LogarithmicJetIdeals.plainJet c Q := by
    simp
  rw [hmap] at hz
  have hcoeff : MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c P -
        OAI.PiExponent.LogarithmicJetIdeals.plainJet c Q) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet c P) -
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet c Q) := by
    simp
  rw [hcoeff] at hz
  exact sub_eq_zero.mp hz