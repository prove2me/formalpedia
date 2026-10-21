-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_homogeneous_coeff
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:26:08.518044+00:00
-- url     : https://prove2.me/submissions/2076c8ae-3dbd-4cab-9781-cc86ff83a893

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_homogeneous_aeval_coeff_of_linear_part
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_sheared_substitution_formula
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_sheared_linear_part

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (n : Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex)
    (hhom : ∀ a : Finsupp (Fin (m + 1)) Nat,
      a ∈ Q.support -> (∑ k : Fin (m + 1), a k) = n)
    (e : Fin (m + 1) -> Nat)
    (he : (∑ k : Fin (m + 1), e k) <= n) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (formalJet center (MvPolynomial.aeval
        (Fin.cases (MvPolynomial.X 0 - MvPolynomial.C 1)
          (fun i => MvPolynomial.X i.succ - MvPolynomial.C (center i) -
            (MvPolynomial.X 0 - MvPolynomial.C 1))) Q)) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) Q := by
  rw [OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_substitution_formula
    center Q]
  let R : Fin (m + 1) -> MvPowerSeries (Fin (m + 1)) Complex :=
    Fin.cases (MvPowerSeries.X 0)
      (fun i => MvPowerSeries.X i.succ +
        liftLogSeries m (PowerSeries.log ℂ) - MvPowerSeries.X 0)
  have hR : ∀ (i : Fin (m + 1)) (d : Fin (m + 1) -> Nat),
      (∑ k : Fin (m + 1), d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R i) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X i) := by
    intro i d hd
    exact OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_linear_part i d hd
  exact OAI.PiExponent.LogarithmicJetIdeals.homogeneous_aeval_coeff_of_linear_part
    R n Q hhom hR e he
