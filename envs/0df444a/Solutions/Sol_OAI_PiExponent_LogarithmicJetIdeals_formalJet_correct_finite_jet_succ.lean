-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_correct_finite_jet_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:10:19.86674+00:00
-- url     : https://prove2.me/submissions/ac950c90-14fd-4e7c-9422-ac7f85401467

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_homogeneous_correction

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (n : Nat)
    (P Q : MvPolynomial (Fin (m + 1)) Complex)
    (hbelow : (e : Fin (m + 1) -> Nat) ->
      (∑ k : Fin (m + 1), e k) < n ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (formalJet center P) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q) :
    Exists fun P' : MvPolynomial (Fin (m + 1)) Complex =>
      ((e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) < n ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P') =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q) ∧
      ((e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= n ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P') =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q) := by
  classical
  let d : (Fin (m + 1) -> Nat) -> Complex := fun e =>
    if (∑ k : Fin (m + 1), e k) = n then
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q -
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (formalJet center P)
    else 0
  have hd : (e : Fin (m + 1) -> Nat) ->
      (∑ k : Fin (m + 1), e k) ≠ n -> d e = 0 := by
    intro e he
    simp only [d, if_neg he]
  obtain ⟨R, hR⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_homogeneous_correction
      center n d hd
  have hagree : (e : Fin (m + 1) -> Nat) ->
      (∑ k : Fin (m + 1), e k) <= n ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (formalJet center (P + R)) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q := by
    intro e he
    rw [map_add, map_add, hR e he]
    by_cases hdeg : (∑ k : Fin (m + 1), e k) = n
    · simp only [d, if_pos hdeg]
      rw [add_comm, sub_add_cancel]
    · rw [hd e hdeg, add_zero]
      exact hbelow e (lt_of_le_of_ne he hdeg)
  refine ⟨P + R, ?_, hagree⟩
  intro e he
  exact hagree e (Nat.le_of_lt he)