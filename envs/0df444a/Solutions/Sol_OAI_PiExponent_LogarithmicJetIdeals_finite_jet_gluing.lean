-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_jet_gluing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:19:23.605793+00:00
-- url     : https://prove2.me/submissions/e3182899-4dfe-41de-97e0-472513e0efb8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_box_jet_gluing

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {iota alpha : Type} [Fintype alpha] [DecidableEq alpha] {m : Nat}
    (center : iota -> Fin m -> Complex) (slot : alpha -> iota)
    (degree : alpha -> Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) -> Exists fun k => Not (center i k = center j k))
    (Q : iota -> MvPolynomial (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (b : alpha) ->
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center (slot b)) P) =
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center (slot b)) (Q (slot b))) := by
  apply Exists.elim
    (OAI.PiExponent.LogarithmicJetIdeals.box_jet_gluing center slot degree hcenters Q)
  intro P hP
  exact Exists.intro P (fun b => hP b (degree b) (fun _ => Nat.le_refl _))