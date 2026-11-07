-- Prove2me | solution 1 for ModernConvex.Relaxations.cast_quadform_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:17:51.215197+00:00
-- url     : https://prove2.me/submissions/92c0ab5f-ca4e-4454-a505-343d49c9b9d6

import Mathlib

/-!
# Transporting a rational certificate to the reals

The PSD oracle runs over `ℚ` and emits, when a matrix is not positive semidefinite, a rational
vector `v` with `v ⬝ᵥ (M *ᵥ v) < 0`. This file shows that the cast of `v` witnesses the same
inequality for the cast of `M` over `ℝ` — so a rational certificate is a real certificate.

The proof is that both operations involved are ring homomorphisms: `RingHom.map_dotProduct` and
`RingHom.map_mulVec` push `ℚ → ℝ` through the dot product and the matrix–vector product, so the
real quadratic form of the cast is the cast of the rational one.
-/

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **A rational certificate is a real certificate.** -/
theorem cast_quadform_neg_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {v : Fin n → ℚ}
    (h : v ⬝ᵥ (M *ᵥ v) < 0) :
    (fun i => (v i : ℝ)) ⬝ᵥ (M.map (fun q : ℚ => (q : ℝ)) *ᵥ (fun i => (v i : ℝ))) < 0 := by
  have key : ((v ⬝ᵥ (M *ᵥ v) : ℚ) : ℝ)
      = (fun i => (v i : ℝ)) ⬝ᵥ (M.map (fun q : ℚ => (q : ℝ)) *ᵥ (fun i => (v i : ℝ))) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul]
  rw [← key]
  exact_mod_cast h

/-- **A rational certificate is a real certificate**, in the form used by the oracle: the cast
matrix is not positive semidefinite. -/
theorem not_posSemidef_of_rat_certificate_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {v : Fin n → ℚ}
    (h : v ⬝ᵥ (M *ᵥ v) < 0) :
    ¬ (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  intro hPSD
  have hnn := hPSD.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
  have hneg := cast_quadform_neg_proof h
  rw [star_trivial] at hnn
  linarith

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {v : Fin n → ℚ}
    (h : v ⬝ᵥ (M *ᵥ v) < 0) :
    (fun i => (v i : ℝ)) ⬝ᵥ (M.map (fun q : ℚ => (q : ℝ)) *ᵥ (fun i => (v i : ℝ))) < 0 :=
  ModernConvex.Relaxations.cast_quadform_neg_proof h
