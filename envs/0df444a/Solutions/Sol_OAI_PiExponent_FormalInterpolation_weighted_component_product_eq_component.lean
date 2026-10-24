-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_product_eq_component
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:54:56.02969+00:00
-- url     : https://prove2.me/submissions/550c5094-fd12-4843-9835-b589c2fbb399

import Mathlib
open scoped BigOperators

theorem solution : ¬ (∀ {d : Nat} (w : Fin d → Rat) (q D : Rat) (m : Nat) (hD : q * (m : Rat) = D) (v : Fin m → MvPolynomial (Fin d) Complex),
    (∏ i, MvPolynomial.weightedHomogeneousComponent (fun j => (w j : ℚ)) q (v i)) = MvPolynomial.weightedHomogeneousComponent (fun j => (w j : ℚ)) D (∏ i, v i)) := by
  intro H
  have h := H (d := 1) (fun _ => 1) 1 2 2 (by norm_num) ![1, MvPolynomial.X 0 ^ 2]
  have h1 : MvPolynomial.weightedHomogeneousComponent (fun _ : Fin 1 => (1 : ℚ)) (1 : ℚ)
      (1 : MvPolynomial (Fin 1) ℂ) = 0 :=
    (MvPolynomial.isWeightedHomogeneous_one ℂ _).weightedHomogeneousComponent_ne _ (by norm_num)
  have hX : MvPolynomial.IsWeightedHomogeneous (fun _ : Fin 1 => (1 : ℚ))
      (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) ℂ) (2 : ℚ) := by
    have := (MvPolynomial.isWeightedHomogeneous_X ℂ (fun _ : Fin 1 => (1 : ℚ)) 0).pow 2
    simpa [two_smul, one_add_one_eq_two] using this
  have h2 := hX.weightedHomogeneousComponent_same
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul] at h
  rw [h1, zero_mul, h2] at h
  exact pow_ne_zero 2 (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin 1)) h.symm
