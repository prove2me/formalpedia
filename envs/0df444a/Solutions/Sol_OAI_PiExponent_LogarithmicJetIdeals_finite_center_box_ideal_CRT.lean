-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_ideal_CRT
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:06:49.615245+00:00
-- url     : https://prove2.me/submissions/305a6075-62f6-42ef-9095-b1acf2fb2ad3

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_rectangularJetIdeals_comaximal_of_centers_differ
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_pairwise_comaximal_ideal_CRT

theorem solution
    {iota : Type} [DecidableEq iota] {m : Nat}
    (active : Finset iota)
    (center : iota -> Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) ->
      Exists fun k => Not (center i k = center j k))
    (localPoly : iota -> MvPolynomial (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (i : iota) -> i ∈ active ->
        P - localPoly i ∈
          OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal (center i) degree := by
  exact OAI.PiExponent.LogarithmicJetIdeals.finite_pairwise_comaximal_ideal_CRT
    active
    (fun i => OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal (center i) degree)
    (by
      intro i j hi hj hij
      exact OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeals_comaximal_of_centers_differ
        (center i) (center j) degree (hcenters i j hij))
    localPoly