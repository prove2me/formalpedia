-- Prove2me | solution 1 for NonAbelianDMNRG.Recursion.eq_40
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:48:50.322572+00:00
-- url     : https://prove2.me/submissions/21de5457-8bef-4766-9871-dc70ae474ecb

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

open Matrix
open scoped Kronecker

theorem solution {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (V : Matrix a a ℂ) (L : Matrix b b ℂ) (hL : Lᴴ * L = 1)
    (R : Matrix (a × b) (a × b) ℂ) :
    WildeQIT.partialTraceRight ((V ⊗ₖ L) * R * (V ⊗ₖ L)ᴴ) =
      V * WildeQIT.partialTraceRight R * Vᴴ := by
  have hL' : ∀ y y' : b, ∑ k, star (L k y') * L k y = if y' = y then 1 else 0 := by
    intro y y'
    have := congrFun (congrFun hL y') y
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  ext i j
  simp only [WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, star_mul']
  simp only [Finset.sum_mul, Finset.mul_sum]
  have step : ∀ x1 x2 x3 : _, ∑ k, ∑ y, V i x3 * L k y * R (x3, y) (x1, x2) *
      (star (V j x1) * star (L k x2)) = V i x3 * R (x3, x2) (x1, x2) * star (V j x1) := by
    intro x1 x2 x3
    rw [Finset.sum_comm]
    have : ∀ y : b, ∑ k, V i x3 * L k y * R (x3, y) (x1, x2) * (star (V j x1) * star (L k x2)) =
        (V i x3 * R (x3, y) (x1, x2) * star (V j x1)) * ∑ k, star (L k x2) * L k y := by
      intro y
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp only [this, hL', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc _ = ∑ x1, ∑ x2, ∑ x3, ∑ k, ∑ y, V i x3 * L k y * R (x3, y) (x1, x2) *
        (star (V j x1) * star (L k x2)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x1 _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x2 _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ x1, ∑ x2, ∑ x3, V i x3 * R (x3, x2) (x1, x2) * star (V j x1) := by
        simp only [step]
    _ = _ := by
        refine Finset.sum_congr rfl fun x1 _ => ?_
        rw [Finset.sum_comm]
