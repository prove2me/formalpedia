-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_of_common_coordinate_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:06:31.394189+00:00
-- url     : https://prove2.me/submissions/3e00088c-ee9f-44cc-bf3b-9dbe2a4f5a9f

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

open scoped BigOperators

variable {N : Nat}

theorem solution {d : Nat} (J : Ideal (MvPolynomial (Fin d) ℂ)) (hN : 0 < N)
    (hpow : ∀ i : Fin d, (MvPolynomial.X i) ^ N ∈ J) :
    Module.Finite ℂ ((MvPolynomial (Fin d) ℂ) ⧸ J) := by
  let P := MvPolynomial (Fin d) ℂ
  let A := P ⧸ J
  let q : P →ₐ[ℂ] A := Ideal.Quotient.mkₐ ℂ J
  let S : Subalgebra ℂ A :=
    Algebra.adjoin ℂ (Set.range fun i : Fin d => q (MvPolynomial.X i))
  have hgen : ∀ f : P, q f ∈ S := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c =>
        change q (algebraMap ℂ P c) ∈ S
        rw [q.commutes c]
        exact S.algebraMap_mem c
    | add f g hf hg =>
        rw [map_add]
        exact S.add_mem hf hg
    | mul_X f i hf =>
        rw [map_mul]
        exact S.mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hS : S = ⊤ := by
    apply le_antisymm
    · exact le_top
    · intro a ha
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ J a
      exact hgen f
  have hfinite : Module.Finite ℂ S := by
    apply Algebra.finite_adjoin_of_finite_of_isIntegral (R := ℂ)
      (A := A) (s := Set.range fun i : Fin d => q (MvPolynomial.X i))
    · exact Set.finite_range _
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      apply IsIntegral.of_pow hN
      have hzero : q (MvPolynomial.X i) ^ N = 0 := by
        rw [← map_pow]
        change Ideal.Quotient.mk J (MvPolynomial.X i ^ N) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpow i)
      simpa [hzero] using (isIntegral_zero : IsIntegral ℂ (0 : A))
  letI := hfinite
  have hsurj : Function.Surjective (S.val : S → A) := by
    intro a
    have ha : a ∈ S := by
      rw [hS]
      trivial
    exact ⟨⟨a, ha⟩, rfl⟩
  exact Module.Finite.of_surjective S.val.toLinearMap hsurj
