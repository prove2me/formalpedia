-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_box_change_of_coordinates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:54:04.448462+00:00
-- url     : https://prove2.me/submissions/856f9f79-0851-491c-a194-5a23903fe975
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_finite_box_surjective
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coeff_eq_of_plainJet_coeff_eq
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {iota : Type} [DecidableEq iota] {m : Nat}
    (active : Finset iota)
    (center : iota -> Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (value : iota -> (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun standardValue : iota -> (Fin (m + 1) -> Nat) -> Complex =>
      (P : MvPolynomial (Fin (m + 1)) Complex) ->
        ((i : iota) -> i ∈ active ->
          (e : Fin (m + 1) -> Nat) ->
            ((k : Fin (m + 1)) -> e k <= ∑ j : Fin (m + 1), degree j) ->
            MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
              (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) P) = standardValue i e) ->
        (i : iota) -> i ∈ active ->
          (e : Fin (m + 1) -> Nat) ->
            ((k : Fin (m + 1)) -> e k <= degree k) ->
            MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
              (formalJet (center i) P) = value i e := by
  classical
  let Q : iota -> MvPolynomial (Fin (m + 1)) Complex := fun i =>
    Classical.choose
      (OAI.PiExponent.LogarithmicJetIdeals.formalJet_finite_box_surjective
        (center i) degree (value i))
  have hQ (i : iota) (e : Fin (m + 1) -> Nat)
      (he : (k : Fin (m + 1)) -> e k <= degree k) :
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (formalJet (center i) (Q i)) = value i e :=
    Classical.choose_spec
      (OAI.PiExponent.LogarithmicJetIdeals.formalJet_finite_box_surjective
        (center i) degree (value i)) e he
  let standardValue : iota -> (Fin (m + 1) -> Nat) -> Complex := fun i e =>
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) (Q i))
  refine ⟨standardValue, ?_⟩
  intro P hP i hi e he
  have hplain :
      (e' : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e' k <= ∑ j : Fin (m + 1), degree j) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e')
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e')
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) (Q i)) := by
    intro e' he'
    change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e')
        (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) P) = standardValue i e'
    rw [hP i hi e' he']
  have htrans :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_eq_of_plainJet_coeff_eq
      (center i) degree P (Q i) hplain e he
  exact htrans.trans (hQ i e he)
