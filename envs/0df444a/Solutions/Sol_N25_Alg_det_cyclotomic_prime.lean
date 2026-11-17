-- Prove2me | solution 1 for N25.Alg.det_cyclotomic_prime
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:44.417243+00:00
-- url     : https://prove2.me/submissions/c67c364e-fafd-41c5-8831-1d45f48000a0

import Mathlib
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

open Polynomial

namespace N25.Alg

/-- The quadratic endomorphism polynomial has determinant the square of 71
on an integral lattice with two fifth-cyclotomic constituents. -/
theorem _root_.solution (A : Matrix (Fin 8) (Fin 8) ℤ)
    (hA : (A.map (Int.castRingHom ℚ)).charpoly = (cyclotomic 5 ℚ) ^ 2) :
    Matrix.det ((2 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) + (4 : ℤ) • A + A * A) =
      (71 : ℤ) ^ 2 := by
  let C := A.map (Int.castRingHom ℚ)
  let B := C.map (Rat.castHom ℝ)
  have hc : B.charpoly = (cyclotomic 5 ℝ) ^ 2 := by
    change (C.map (Rat.castHom ℝ)).charpoly = _
    rw [Matrix.charpoly_map, show C.charpoly = (cyclotomic 5 ℚ) ^ 2 from hA,
      Polynomial.map_pow, Polynomial.map_cyclotomic]
  let s : ℝ := Real.sqrt 2
  let r : ℝ := -2 + s
  let t : ℝ := -2 - s
  have hs : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : r + t = -4 := by dsimp [r, t]; ring
  have hmul : r * t = 2 := by dsimp [r, t]; nlinarith only [hs]
  have hfactor :
      (r • (1 : Matrix (Fin 8) (Fin 8) ℝ) - B) * (t • 1 - B) =
        (2 : ℝ) • 1 + (4 : ℝ) • B + B * B := by
    calc
      _ = (r * t) • (1 : Matrix (Fin 8) (Fin 8) ℝ) - (r + t) • B + B * B := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
          mul_one]
        module
      _ = _ := by rw [hmul, hsum]; module
  have hphi : cyclotomic 5 ℝ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [Polynomial.cyclotomic_prime]
    simp [Finset.sum_range_succ]
    ring
  have hr : (cyclotomic 5 ℝ).eval r = 53 - 37 * s := by
    rw [hphi]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    dsimp [r]
    linear_combination (s ^ 2 - 7 * s + 21) * hs
  have ht : (cyclotomic 5 ℝ).eval t = 53 + 37 * s := by
    rw [hphi]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    dsimp [t]
    linear_combination (s ^ 2 + 7 * s + 21) * hs
  have hdet : Matrix.det ((2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) +
      (4 : ℝ) • B + B * B) = (71 : ℝ) ^ 2 := by
    rw [← hfactor, Matrix.det_mul]
    have heval (x : ℝ) :
        Matrix.det (x • (1 : Matrix (Fin 8) (Fin 8) ℝ) - B) =
          ((cyclotomic 5 ℝ).eval x) ^ 2 := by
      have hscalar : Matrix.scalar (Fin 8) x = x • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
      rw [← hscalar, ← Matrix.eval_charpoly, hc, Polynomial.eval_pow]
    rw [heval r, heval t, hr, ht]
    rw [← mul_pow]
    have hprod : (53 - 37 * s) * (53 + 37 * s) = 71 := by nlinarith only [hs]
    rw [hprod]
  have hB : B = A.map (Int.castRingHom ℝ) := by
    ext i j
    simp [B, C]
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_pow, Int.cast_ofNat, Int.cast_det]
  refine (congrArg Matrix.det ?_).trans hdet
  rw [hB]
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, Matrix.ofNat_apply, Matrix.one_apply]

end N25.Alg
