-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.sum_sigma_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:45:27.851591+00:00
-- url     : https://prove2.me/submissions/d56fca88-3226-4a76-9fa8-3485c41a3511

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ι → ℕ}
    (t : Finset (Σ i, Fin (q i))) :
    (∑ i, (t.filter fun x : Σ j, Fin (q j) => x.1 = i).card) = t.card := by
  classical
  simpa using
    (Finset.card_eq_sum_card_fiberwise
      (f := fun x : Σ i, Fin (q i) => x.1)
      (s := t)
      (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm