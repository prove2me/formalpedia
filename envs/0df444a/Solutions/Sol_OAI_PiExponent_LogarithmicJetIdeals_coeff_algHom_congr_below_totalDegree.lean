-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_algHom_congr_below_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:33:14.543774+00:00
-- url     : https://prove2.me/submissions/e8c5903a-afef-48e4-b845-305a85d47bd1

import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem solution
    {σ τ A : Type*} [Fintype τ] [CommSemiring A]
    (F G : MvPolynomial σ A →ₐ[A] MvPowerSeries τ A) (T : ℕ)
    (h : ∀ (i : σ) (d : τ → ℕ), (∑ j, d j) < T →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (F (MvPolynomial.X i)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (G (MvPolynomial.X i)))
    (P : MvPolynomial σ A) (d : τ → ℕ) (hd : (∑ j, d j) < T) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (F P) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (G P) := by
  classical
  induction P using MvPolynomial.induction_on generalizing d with
  | C a =>
      simp only [MvPolynomial.algHom_C]
  | add p q hp hq =>
      simp only [map_add, hp d hd, hq d hd]
  | mul_X p i hp =>
      simp only [map_mul, MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl ?_
      intro ab hab
      have hab' : ab.1 + ab.2 = Finsupp.equivFunOnFinite.symm d :=
        Finset.mem_antidiagonal.mp hab
      have habj (j : τ) : ab.1 j + ab.2 j = d j := by
        have hj := congrArg (fun e : τ →₀ ℕ => e j) hab'
        simpa only [Finsupp.add_apply, Finsupp.coe_equivFunOnFinite_symm] using hj
      have hfst : (∑ j, ab.1 j) < T := by
        refine lt_of_le_of_lt (Finset.sum_le_sum fun j _ => ?_) hd
        calc
          ab.1 j ≤ ab.1 j + ab.2 j := Nat.le_add_right _ _
          _ = d j := habj j
      have hsnd : (∑ j, ab.2 j) < T := by
        refine lt_of_le_of_lt (Finset.sum_le_sum fun j _ => ?_) hd
        calc
          ab.2 j ≤ ab.1 j + ab.2 j := Nat.le_add_left _ _
          _ = d j := habj j
      apply congrArg₂ (fun a b : A => a * b)
      · simpa only [Finsupp.equivFunOnFinite_symm_coe] using hp (⇑ab.1) hfst
      · simpa only [Finsupp.equivFunOnFinite_symm_coe] using h i (⇑ab.2) hsnd