-- Prove2me | solution 1 for NesterovRCD.Sublinear.lemma1_diag
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:27:20.01467+00:00
-- url     : https://prove2.me/submissions/2493af04-ca2d-4223-8810-494753003957

import Mathlib
set_option autoImplicit false
open Matrix

theorem pair_aux {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (x : Fin m → ℝ)
    (i j : Fin m) : 2 * (x i * A i j * x j) ≤ A i i * x i ^ 2 + A j j * x j ^ 2 := by
  by_cases hij : i = j
  · subst hij; nlinarith
  · have h := hA.dotProduct_mulVec_nonneg (Pi.single i (x i) - Pi.single j (x j))
    have hs : A j i = A i j := by
      have := hA.1.apply i j
      simpa using this
    simp [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, Matrix.mulVec_single,
      dotProduct_single, single_dotProduct, hij, Ne.symm hij, hs] at h
    nlinarith [h]

theorem solution {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (x : Fin m → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ (m : ℝ) * ∑ j, A j j * x j ^ 2 := by
  have h1 : x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, x i * A i j * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, ∑ j, (A i i * x i ^ 2 + A j j * x j ^ 2) = 2 * ((m : ℝ) * ∑ j, A j j * x j ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have h3 : ∑ i, ∑ j, 2 * (x i * A i j * x j) ≤ ∑ i, ∑ j, (A i i * x i ^ 2 + A j j * x j ^ 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pair_aux A hA x i j
  have h4 : ∑ i, ∑ j, 2 * (x i * A i j * x j) = 2 * ∑ i, ∑ j, x i * A i j * x j := by
    simp [Finset.mul_sum]
  linarith
