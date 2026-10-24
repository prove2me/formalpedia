-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers_in_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:43:28.194027+00:00
-- url     : https://prove2.me/submissions/368db2b2-cc02-4912-853d-1648d5bf7fdf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

open scoped BigOperators

theorem solution
    (d : Nat) (m : Nat) (p : Fin m → MvPolynomial (Fin d) Complex)
    (hpow : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      MvPolynomial.X i ^ N ∈ Ideal.span (Set.range p)) :
    Module.Finite Complex
      (MvPolynomial (Fin d) Complex ⧸ Ideal.span (Set.range p)) := by
  let P := MvPolynomial (Fin d) Complex
  let I : Ideal P := Ideal.span (Set.range p)
  let A := P ⧸ I
  let q : P →ₐ[Complex] A := Ideal.Quotient.mkₐ Complex I
  let S : Subalgebra Complex A :=
    Algebra.adjoin Complex (Set.range fun i : Fin d => q (MvPolynomial.X i))
  have hgen : ∀ f : P, q f ∈ S := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c =>
      change q (algebraMap Complex P c) ∈ S
      rw [q.commutes c]
      exact S.algebraMap_mem c
    | add f g hf hg =>
      rw [map_add]
      exact S.add_mem hf hg
    | mul_X f i hf =>
      rw [map_mul]
      simpa [mul_comm] using S.mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hS : S = ⊤ := by
    apply top_unique
    intro a ha
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective Complex I a
    exact hgen f
  have hfinite : Module.Finite Complex S := by
    apply Algebra.finite_adjoin_of_finite_of_isIntegral (R := Complex)
      (A := A) (s := Set.range fun i : Fin d => q (MvPolynomial.X i))
    · exact Set.finite_range _
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨N, hN, hmem⟩ := hpow i
      apply IsIntegral.of_pow hN
      have hzero : q (MvPolynomial.X i) ^ N = 0 := by
        rw [← map_pow]
        change Ideal.Quotient.mk I (MvPolynomial.X i ^ N) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      simpa [hzero] using (isIntegral_zero : IsIntegral Complex (0 : A))
  letI := hfinite
  have hsurj : Function.Surjective (S.val : S → A) := by
    intro a
    have ha : a ∈ S := by
      rw [hS]
      trivial
    exact ⟨⟨a, ha⟩, rfl⟩
  exact Module.Finite.of_surjective S.val.toLinearMap hsurj