-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_finite_box_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:59:27.879544+00:00
-- url     : https://prove2.me/submissions/7cfe43db-fa20-4639-ac3c-957412f01641
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_total_degree_surjective

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (value : (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e k <= degree k) ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet center P) = value e := by
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_total_degree_surjective
      center (∑ k : Fin (m + 1), degree k) value
  refine ⟨P, ?_⟩
  intro e he
  apply hP e
  exact Finset.sum_le_sum fun k _ => he k