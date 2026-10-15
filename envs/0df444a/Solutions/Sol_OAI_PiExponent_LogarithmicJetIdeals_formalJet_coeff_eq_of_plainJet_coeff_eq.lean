-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_eq_of_plainJet_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:04:39.178258+00:00
-- url     : https://prove2.me/submissions/bdffb92b-6b70-461e-8282-a300e0333a9f

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

private theorem constantCoeff_liftLogSeries (m : Nat) (f : PowerSeries Complex) :
    MvPowerSeries.constantCoeff (liftLogSeries m f) = PowerSeries.constantCoeff f := by
  have hfin : MvPowerSeries.finSuccEquiv Complex m (liftLogSeries m f) =
      PowerSeries.map MvPowerSeries.C f := by
    exact (MvPowerSeries.finSuccEquiv Complex m).apply_symm_apply _
  have hc := MvPowerSeries.coeff_coeff_finSuccEquiv
    (liftLogSeries m f) (k := 0) (x := 0)
  rw [hfin, PowerSeries.coeff_map, Finsupp.cons_zero_zero] at hc
  simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.constantCoeff_C, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hc.symm

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (P Q : MvPolynomial (Fin (m + 1)) Complex)
    (hPQ : (e : Fin (m + 1) -> Nat) ->
      ((k : Fin (m + 1)) -> e k <= ∑ j : Fin (m + 1), degree j) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet center Q)) :
    (e : Fin (m + 1) -> Nat) ->
      ((k : Fin (m + 1)) -> e k <= degree k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center Q) := by
  classical
  let a : Fin (m + 1) -> MvPowerSeries (Fin (m + 1)) Complex :=
    Fin.cases (MvPowerSeries.X 0)
      (fun i => MvPowerSeries.X i.succ + liftLogSeries m (PowerSeries.log Complex))
  have ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [a]
    · simp [a, constantCoeff_liftLogSeries]
  have ha : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  let S : MvPowerSeries (Fin (m + 1)) Complex →ₐ[Complex]
      MvPowerSeries (Fin (m + 1)) Complex := MvPowerSeries.substAlgHom ha
  have hSC (z : Complex) : S (MvPowerSeries.C z) = MvPowerSeries.C z :=
    S.commutes z
  have hSX (i : Fin (m + 1)) : S (MvPowerSeries.X i) = a i :=
    MvPowerSeries.substAlgHom_X ha i
  have hcomp : S.comp (OAI.PiExponent.LogarithmicJetIdeals.plainJet center) =
      formalJet center := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [AlgHom.comp_apply, OAI.PiExponent.LogarithmicJetIdeals.plainJet,
        formalJet, MvPolynomial.aeval_X, Fin.cases_zero, map_add, map_one, hSX, a]
    · simp only [AlgHom.comp_apply, OAI.PiExponent.LogarithmicJetIdeals.plainJet,
        formalJet, MvPolynomial.aeval_X, Fin.cases_succ, map_add, hSC, hSX]
      change MvPowerSeries.C (center j) +
          (MvPowerSeries.X j.succ + liftLogSeries m (PowerSeries.log Complex)) =
        MvPowerSeries.C (center j) + MvPowerSeries.X j.succ +
          liftLogSeries m (PowerSeries.log Complex)
      exact (add_assoc _ _ _).symm
  have hjet (A : MvPolynomial (Fin (m + 1)) Complex) :
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet center A).subst a =
        formalJet center A := by
    rw [← MvPowerSeries.substAlgHom_apply ha]
    exact DFunLike.congr_fun hcomp A
  let N : Nat := ∑ j : Fin (m + 1), degree j
  have htrunc :
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet center P).truncTotal (N + 1) =
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet center Q).truncTotal (N + 1) := by
    ext d
    by_cases hd : d.degree < N + 1
    · rw [MvPowerSeries.coeff_truncTotal _ hd, MvPowerSeries.coeff_truncTotal _ hd]
      have hb : ∀ j, d j ≤ ∑ k : Fin (m + 1), degree k := by
        intro j
        have hj : d j ≤ d.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (fun k hk => Nat.zero_le (d k)) (Finset.mem_univ j)
        exact le_trans hj (Nat.lt_succ_iff.mp hd)
      simpa only [Finsupp.equivFunOnFinite_symm_coe] using hPQ (fun j => d j) hb
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (not_lt.mp hd),
        MvPowerSeries.coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
  have hout :
      ((OAI.PiExponent.LogarithmicJetIdeals.plainJet center P).subst a).truncTotal
          (N + 1) =
      ((OAI.PiExponent.LogarithmicJetIdeals.plainJet center Q).subst a).truncTotal
          (N + 1) := by
    rw [MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
          (f := OAI.PiExponent.LogarithmicJetIdeals.plainJet center P) ha0,
        MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
          (f := OAI.PiExponent.LogarithmicJetIdeals.plainJet center Q) ha0,
        htrunc]
  rw [hjet P, hjet Q] at hout
  intro e he
  have hedeg : (Finsupp.equivFunOnFinite.symm e).degree < N + 1 := by
    rw [Finsupp.degree_eq_sum]
    change (∑ j : Fin (m + 1), e j) < N + 1
    apply Nat.lt_succ_of_le
    exact Finset.sum_le_sum (fun j hj => he j)
  have hc := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)) hout
  rw [MvPowerSeries.coeff_truncTotal _ hedeg,
      MvPowerSeries.coeff_truncTotal _ hedeg] at hc
  exact hc