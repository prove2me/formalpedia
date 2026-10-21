-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_jet_surjective_on_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:55:44.418528+00:00
-- url     : https://prove2.me/submissions/2000ae15-b1a6-4092-993d-e33006e6d25b

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_correct_finite_jet_succ

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (N : Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q := by
  have hAll : ∀ n : Nat,
      Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
        (e : Fin (m + 1) -> Nat) ->
          (∑ k : Fin (m + 1), e k) <= n ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet center P) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q := by
    intro n
    induction n with
    | zero =>
        have hbelow : ∀ e : Fin (m + 1) -> Nat,
            (∑ k : Fin (m + 1), e k) < 0 ->
              MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
                (formalJet center (0 : MvPolynomial (Fin (m + 1)) Complex)) =
              MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q := by
          intro e he
          exact False.elim (Nat.not_lt_zero _ he)
        obtain ⟨P, hparts⟩ :=
          OAI.PiExponent.LogarithmicJetIdeals.formalJet_correct_finite_jet_succ
            center 0 (0 : MvPolynomial (Fin (m + 1)) Complex) Q hbelow
        exact ⟨P, hparts.2⟩
    | succ n ih =>
        obtain ⟨P, hP⟩ := ih
        have hbelow : ∀ e : Fin (m + 1) -> Nat,
            (∑ k : Fin (m + 1), e k) < n + 1 ->
              MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
                (formalJet center P) =
              MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q := by
          intro e he
          exact hP e (Nat.le_of_lt_succ he)
        obtain ⟨P', hparts⟩ :=
          OAI.PiExponent.LogarithmicJetIdeals.formalJet_correct_finite_jet_succ
            center (n + 1) P Q hbelow
        exact ⟨P', hparts.2⟩
  exact hAll N