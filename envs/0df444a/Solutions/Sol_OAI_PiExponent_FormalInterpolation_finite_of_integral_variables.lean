-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_of_integral_variables
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:34:56.374012+00:00
-- url     : https://prove2.me/submissions/a49d5c5a-1f04-4d81-9e6e-2d3fb5ed6e99

import Mathlib

section

open MvPolynomial

namespace PiL6

theorem fin_int {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hcoords : ∀ i : Fin d,
      IsIntegral A (MvPolynomial.X i : MvPolynomial (Fin d) Complex)) :
    Module.Finite A (MvPolynomial (Fin d) Complex) := by
  have htop : Algebra.adjoin A (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ)) = ⊤ := by
    rw [eq_top_iff]
    intro p _
    have hp : p ∈ Algebra.adjoin ℂ (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ)) := by
      rw [MvPolynomial.adjoin_range_X]; trivial
    have hle : Algebra.adjoin ℂ (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ)) ≤
        (Algebra.adjoin A (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ))).restrictScalars ℂ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle hp
  have hfg := fg_adjoin_of_finite (Set.finite_range (X : Fin d → MvPolynomial (Fin d) ℂ))
    (R := A) (by rintro _ ⟨i, rfl⟩; exact hcoords i)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

theorem coord_dep {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ))
    [Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I)] (i : Fin d) :
    ∃ K : Nat, ∃ c : Fin (K + 1) → ℂ,
      (∃ n : Fin (K + 1), c n ≠ 0) ∧
      (∑ n : Fin (K + 1), MvPolynomial.C (c n) *
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat)) ∈ I := by
  set K := Module.finrank ℂ (MvPolynomial (Fin d) ℂ ⧸ I)
  let v : Fin (K + 1) → MvPolynomial (Fin d) ℂ ⧸ I := fun n => Ideal.Quotient.mkₐ ℂ I (X i ^ (n : ℕ))
  have hnli : ¬ LinearIndependent ℂ v := by
    intro h
    have := h.fintype_card_le_finrank
    simp [K] at this
  obtain ⟨g, hg, n, hn⟩ := Fintype.not_linearIndependent_iff.1 hnli
  refine ⟨K, g, ⟨n, hn⟩, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : Ideal.Quotient.mk I (∑ n : Fin (K + 1), C (g n) * X i ^ (n : ℕ)) = ∑ n, g n • v n := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.C_mul', ← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]
  rw [this, hg]

theorem mono_quot (d : Nat) (N : Fin d → Nat) (hN : ∀ i, 0 < N i) : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range (fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N i))) := by
  set J := Ideal.span (Set.range (fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N i))
  let f := Ideal.Quotient.mkₐ ℂ J
  have htop : Algebra.adjoin ℂ (f '' Set.range (X : Fin d → MvPolynomial (Fin d) ℂ)) = ⊤ := by
    rw [Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top f).2 (Ideal.Quotient.mkₐ_surjective ℂ J)
  have hfg := fg_adjoin_of_finite ((Set.finite_range (X : Fin d → MvPolynomial (Fin d) ℂ)).image f)
    (R := ℂ) (by
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      refine IsIntegral.of_pow (hN i) ?_
      have : f (X i) ^ N i = 0 := by
        rw [← map_pow, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span ⟨i, rfl⟩
      rw [this]; exact isIntegral_zero)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

theorem const_zero {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (i : Fin d) (q : Polynomial ℂ)
    (hqI : Polynomial.aeval (MvPolynomial.X i) q ∈ Ideal.span (Set.range p)) :
    q.coeff 0 = 0 := by
  have hle : Ideal.span (Set.range p) ≤ RingHom.ker (MvPolynomial.constantCoeff (R := ℂ) (σ := Fin d)) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.constantCoeff_eq]
    by_contra h
    have := hp j h
    simp at this
    exact absurd this (by exact_mod_cast hD.ne)
  have := hle hqI
  rw [RingHom.mem_ker, Polynomial.aeval_def, Polynomial.hom_eval₂] at this
  rw [Polynomial.coeff_zero_eq_eval_zero]
  convert this using 1
  simp [Polynomial.eval₂_eq_eval_map]

end PiL6

end



theorem solution
    {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hvars : ∀ i : Fin d, IsIntegral A (MvPolynomial.X (R := Complex) i)) :
    Module.Finite A (MvPolynomial (Fin d) Complex) := by
  apply PiL6.fin_int <;> assumption
