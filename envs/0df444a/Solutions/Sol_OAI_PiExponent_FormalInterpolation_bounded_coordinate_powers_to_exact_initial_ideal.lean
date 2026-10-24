-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_to_exact_initial_ideal
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:15:29.342871+00:00
-- url     : https://prove2.me/submissions/db191928-1443-4441-9a2a-d1774025df34

import Mathlib

open scoped BigOperators

theorem solution : ¬ (∀ {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (R : Real)
    (hsections : ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * R ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ I ^ s ∧
        (n : Real) * (w i : Real) ≤ (B : Real)),
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * R ∧
      0 < D ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span
          {h : MvPolynomial (Fin d) Complex |
            ∃ g : MvPolynomial (Fin d) Complex,
              g ∈ I ^ s ∧
              (∀ a ∈ g.support,
                ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) (D : ℚ) g}) := by
  intro H
  obtain ⟨s, _, D, _, hD0, hall⟩ := H (d := 1) ⊤ (fun _ => 0) 1
    ⟨1, one_pos, 0, by norm_num, fun i => ⟨1, one_pos, by simp, by simp⟩⟩
  obtain ⟨n, _, hmem⟩ := hall 0
  have hle : Ideal.span {h : MvPolynomial (Fin 1) Complex |
            ∃ g : MvPolynomial (Fin 1) Complex,
              g ∈ (⊤ : Ideal (MvPolynomial (Fin 1) Complex)) ^ s ∧
              (∀ a ∈ g.support,
                ∑ k, (((fun _ => (0:ℚ)) : Fin 1 → ℚ) k : Real) * (a k : Real) ≤ (D : Real)) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (((fun _ => (0:ℚ)) : Fin 1 → ℚ) k : ℚ)) (D : ℚ) g} ≤ ⊥ := by
    rw [Ideal.span_le]
    rintro _ ⟨g, _, _, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_bot]
    ext a
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_neg]
    · simp
    · have : (D : ℚ) ≠ 0 := by exact_mod_cast hD0.ne'
      simpa [Finsupp.weight_apply] using this.symm
  have := hle hmem
  rw [Ideal.mem_bot] at this
  exact pow_ne_zero n (MvPolynomial.X_ne_zero 0) this
