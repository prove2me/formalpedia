-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.plain_jet_box_local_realization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T21:32:46.310421+00:00
-- url     : https://prove2.me/submissions/deb296ea-0e38-4c72-9e73-cbb835c264de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plain_jet_shifted_monomial_sum_coeff

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (c : Fin m -> Complex) (degree : Fin (m + 1) -> Nat)
    (value : (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun Q : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e k <= degree k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet c Q) = value e := by
  classical
  let s : Finset (Fin (m + 1) -> Nat) :=
    Finset.univ.image
      (fun d : (k : Fin (m + 1)) -> Fin (degree k + 1) => fun k => (d k).val)
  refine Exists.intro
    (Finset.sum s (fun d => MvPolynomial.C (value d) *
      Finset.prod Finset.univ (fun k : Fin (m + 1) => (MvPolynomial.X k -
        MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k))
          ^ d k))) ?_
  intro e he
  have heS : e ∈ s := by
    apply Finset.mem_image.mpr
    refine Exists.intro (fun k => Fin.mk (e k) (Nat.lt_succ_of_le (he k))) ?_
    exact And.intro (Finset.mem_univ _) (by funext k; rfl)
  simpa only [if_pos heS] using
    (OAI.PiExponent.LogarithmicJetIdeals.plain_jet_shifted_monomial_sum_coeff
      (c := c) (s := s) (a := value) (e := e))
