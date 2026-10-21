-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.sigma_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:49:49.807311+00:00
-- url     : https://prove2.me/submissions/d74213f3-12b1-48d2-a9f8-c11bd2cde26c

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (i : ι) :
    (Finset.univ.filter (fun x : Σ j, Fin (q j) => x.1 = i)).card = q i := by
  classical
  let fiberEquiv : {x : Σ j, Fin (q j) // x.1 = i} ≃ Fin (q i) := {
    toFun := fun x => Fin.cast (congrArg q x.2) x.1.2
    invFun := fun k => ⟨⟨i, k⟩, rfl⟩
    left_inv := by
      intro x
      apply Subtype.ext
      rcases x with ⟨⟨j, k⟩, h⟩
      cases h
      rfl
    right_inv := by
      intro k
      rfl
  }
  calc
    (Finset.univ.filter (fun x : Σ j, Fin (q j) => x.1 = i)).card =
        Fintype.card {x : Σ j, Fin (q j) // x.1 = i} := by
          symm
          rw [Fintype.card_subtype]
    _ = Fintype.card (Fin (q i)) := Fintype.card_congr fiberEquiv
    _ = q i := Fintype.card_fin _