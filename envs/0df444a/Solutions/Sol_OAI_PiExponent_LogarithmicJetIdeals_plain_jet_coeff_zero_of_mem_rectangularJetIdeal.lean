-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.plain_jet_coeff_zero_of_mem_rectangularJetIdeal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:10:29.71943+00:00
-- url     : https://prove2.me/submissions/803fd72b-17b9-4cc0-9bca-0c3a20fb01ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plainJet_mem_span_X_pow_of_mem_rectangularJetIdeal
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_zero_of_mem_coordinate_power_ideal

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (c : Fin m -> Complex) (degree : Fin (m + 1) -> Nat)
    (R : MvPolynomial (Fin (m + 1)) Complex)
    (h : R ∈ OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal c degree)
    (e : Fin (m + 1) -> Nat)
    (he : (k : Fin (m + 1)) -> e k <= degree k) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c R) = 0 := by
  have hS :=
    OAI.PiExponent.LogarithmicJetIdeals.plainJet_mem_span_X_pow_of_mem_rectangularJetIdeal
      c degree R h
  exact OAI.PiExponent.LogarithmicJetIdeals.coeff_zero_of_mem_coordinate_power_ideal
    degree (OAI.PiExponent.LogarithmicJetIdeals.plainJet c R) hS e he