-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_homogeneous_finite_colength_coordinate_powers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:49:49.274985+00:00
-- url     : https://prove2.me/submissions/8f88b13b-f060-4f4a-80aa-33b154a2330a

import Mathlib

open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open MvPolynomial in
theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (s : Nat) (q : Rat) (hq : 0 < q)
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸
      Ideal.span (Set.range (fun (p :
        {g : MvPolynomial (Fin d) Complex //
          g ∈ I ^ s ∧
          ∀ a ∈ g.support,
            ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
        MvPolynomial.weightedHomogeneousComponent
          (fun j => (w j : ℚ)) q p.1)))) :
    ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      MvPolynomial.X i ^ n ∈ Ideal.span (Set.range (fun (p :
        {g : MvPolynomial (Fin d) Complex //
          g ∈ I ^ s ∧
          ∀ a ∈ g.support,
            ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
        MvPolynomial.weightedHomogeneousComponent
          (fun j => (w j : ℚ)) q p.1)) := by
  classical
  intro i
  set J := Ideal.span (Set.range (fun (p :
        {g : MvPolynomial (Fin d) Complex //
          g ∈ I ^ s ∧
          ∀ a ∈ g.support,
            ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
        MvPolynomial.weightedHomogeneousComponent
          (fun j => (w j : ℚ)) q p.1)) with hJ
  -- homogeneity
  have hhom : J.IsHomogeneous (weightedHomogeneousSubmodule ℂ (fun j => (w j : ℚ))) := by
    apply Ideal.homogeneous_span
    rintro x ⟨p, rfl⟩
    exact ⟨q, weightedHomogeneousComponent_mem _ _ _⟩
  -- no constants
  have hconst : ∀ x ∈ J, constantCoeff x = 0 := by
    intro x hx
    have : J ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin d) ℂ →+* ℂ) := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      rw [constantCoeff_eq, coeff_weightedHomogeneousComponent]
      rw [if_neg]
      simp only [map_zero]
      exact fun h => (ne_of_lt hq) h
    exact this hx
  -- linear dependence of powers
  have hdep : ¬ LinearIndependent ℂ
      (fun n : ℕ => Ideal.Quotient.mk J (X i ^ n : MvPolynomial (Fin d) ℂ)) :=
    Module.Finite.not_linearIndependent_of_infinite _
  rw [not_linearIndependent_iff] at hdep
  obtain ⟨S, a, hsum, n0, hn0, ha0⟩ := hdep
  set F : MvPolynomial (Fin d) ℂ := ∑ n ∈ S, C (a n) * X i ^ n with hF
  have hFJ : F ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [hF, map_sum]
    convert hsum using 2 with n _
    rw [← smul_eq_C_mul, ← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]
  have hwi : (w i : ℚ) ≠ 0 := by
    have := hw i; intro h; rw [h] at this; simp at this
  have hhomX : ∀ n : ℕ, (X i ^ n : MvPolynomial (Fin d) ℂ) ∈
      weightedHomogeneousSubmodule ℂ (fun j => (w j : ℚ)) (n • (w i : ℚ)) := by
    intro n
    exact (isWeightedHomogeneous_X ℂ (fun j => (w j : ℚ)) i).pow n
  have hcomp : weightedHomogeneousComponent (fun j => (w j : ℚ)) (n0 • (w i : ℚ)) F =
      C (a n0) * X i ^ n0 := by
    rw [hF, map_sum]
    rw [Finset.sum_eq_single n0]
    · rw [← smul_eq_C_mul, map_smul, weightedHomogeneousComponent_of_mem (hhomX n0), if_pos rfl,
        smul_eq_C_mul]
    · intro n _ hn
      rw [← smul_eq_C_mul, map_smul, weightedHomogeneousComponent_of_mem (hhomX n), if_neg, smul_zero]
      intro h
      apply hn
      have : (n0 : ℚ) * w i = n * w i := by simpa [nsmul_eq_mul] using h
      exact_mod_cast (mul_right_cancel₀ hwi this).symm
    · intro h; exact absurd hn0 h
  have hmem := weightedHomogeneousComponent_mem_of_mem ℂ (fun j => (w j : ℚ)) hhom hFJ
    (n0 • (w i : ℚ))
  rw [hcomp] at hmem
  have hXmem : (X i ^ n0 : MvPolynomial (Fin d) ℂ) ∈ J := by
    have := J.mul_mem_left (C (a n0)⁻¹) hmem
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha0, C_1, one_mul] at this
  refine ⟨n0, Nat.pos_of_ne_zero ?_, hXmem⟩
  intro h0
  rw [h0, pow_zero] at hXmem
  have := hconst _ hXmem
  simp at this
