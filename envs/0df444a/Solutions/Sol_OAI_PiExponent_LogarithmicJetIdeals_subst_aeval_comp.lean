-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.subst_aeval_comp
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:05:03.215749+00:00
-- url     : https://prove2.me/submissions/2015a29c-417c-4972-b64d-7fc8384d6624

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution

theorem solution
    {m : ℕ}
    (a b : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (ha : MvPowerSeries.HasSubst a) (hb : MvPowerSeries.HasSubst b)
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst b (MvPolynomial.aeval a Q) =
      MvPolynomial.aeval (fun i => MvPowerSeries.subst b (a i)) Q := by
  simpa only [← MvPowerSeries.substAlgHom_apply hb] using
    (MvPolynomial.comp_aeval_apply a (MvPowerSeries.substAlgHom hb) Q)