-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_sum_coeff_of_terms
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T06:37:11.027147+00:00
-- url     : https://prove2.me/submissions/bb932322-75a6-4954-9de6-86081523f86d

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators
set_option autoImplicit false

theorem solution
    {n : Nat}
    (f : (Fin n → Nat) → MvPowerSeries (Fin n) Complex)
    (value : (Fin n → Nat) → Complex)
    (m : Nat)
    (S : Finset (Fin n → Nat))
    (hS : ∀ d : Fin n → Nat, d ∈ S ↔ (∑ k, d k) = m)
    (e : Fin n → Nat)
    (he : (∑ k, e k) ≤ m)
    (hterm : ∀ d ∈ S,
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (f d) =
        (if d = e then value d else 0)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (∑ d ∈ S, f d) =
      (if (∑ k, e k) = m then value e else 0) := by
  classical
  calc
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (∑ d ∈ S, f d) =
        ∑ d ∈ S, MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (f d) := by
      simp only [map_sum]
    _ = ∑ d ∈ S, if d = e then value d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hterm d hd
    _ = if (∑ k, e k) = m then value e else 0 := by
      by_cases hdegree : (∑ k, e k) = m
      · have hmem : e ∈ S := (hS e).mpr hdegree
        simp [hdegree, hmem]
      · have hnot : e ∉ S := fun hmem => hdegree ((hS e).mp hmem)
        simp [hdegree, hnot]

#print axioms solution
