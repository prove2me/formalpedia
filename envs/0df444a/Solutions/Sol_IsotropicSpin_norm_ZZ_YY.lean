-- Prove2me | solution 1 for IsotropicSpin.norm_ZZ_YY
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T23:30:49.180287+00:00
-- url     : https://prove2.me/submissions/21aafaad-632e-4147-b6d5-600f48c8a499

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_yMat
import Definitions.Def_IsotropicSpin_zMat

open scoped Matrix Matrix.Norms.L2Operator
open IsotropicSpin


/-- **The norms `‖ZZ†‖ = ‖YY†‖ = 1`**, Alicki, arXiv:quant-ph/0402080v1, §2, proof of Theorem 1,
p. 3 (after (21)): "Because ZZ† is a positive matrix with trace equal 2 than it follows that its
norm ‖ZZ†‖ = ‖YY†‖ = 1".

1. `‖Z Z†‖ = 1` for all real `α, β`, with `Z` of (19);
2. `‖Y Y†‖ = 1` for every unit vector `ξ ∈ ℂ³`, with `Y = Σ_k ξ_k S_k` of (18).

**Formalization Note** `‖·‖` is the operator norm induced by the Euclidean norm
(`Matrix.Norms.L2Operator`). -/
theorem solution :
    (∀ α β : ℝ, ‖zMat α β * (zMat α β)ᴴ‖ = 1) ∧
    (∀ ξ : Fin 3 → ℂ, WHAdditivity.Renyi.IsUnitVector ξ → ‖yMat ξ * (yMat ξ)ᴴ‖ = 1) := by
  classical
  have hy (ξ : Fin 3 → ℂ) (hξ : WHAdditivity.Renyi.IsUnitVector ξ) :
      ‖yMat ξ * (yMat ξ)ᴴ‖ = 1 := by
    have hR : Complex.normSq (ξ 0) + Complex.normSq (ξ 1) + Complex.normSq (ξ 2) = 1 := by
      simpa only [WHAdditivity.Renyi.IsUnitVector, Fin.sum_univ_three] using hξ
    have hN : ξ 0 * (starRingEnd ℂ) (ξ 0) + ξ 1 * (starRingEnd ℂ) (ξ 1) +
        ξ 2 * (starRingEnd ℂ) (ξ 2) = 1 := by
      simpa only [Complex.mul_conj, ← Complex.ofReal_add, Complex.ofReal_one]
        using congrArg (fun r : ℝ => (r : ℂ)) hR
    have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have ht : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
      rw [inv_pow, hs]
      norm_num
    let t : ℂ := (Real.sqrt 2 : ℂ)⁻¹
    let u : Fin 3 → ℂ := ![-t * (starRingEnd ℂ) (ξ 0 + Complex.I * ξ 1),
      (starRingEnd ℂ) (ξ 2), t * (starRingEnd ℂ) (ξ 0 - Complex.I * ξ 1)]
    let Q : Matrix (Fin 3) (Fin 3) ℂ := Matrix.vecMulVec u (star u)
    let P : Matrix (Fin 3) (Fin 3) ℂ := yMat ξ * (yMat ξ)ᴴ
    have hu : star u ⬝ᵥ u = 1 := by
      norm_num [u, t, dotProduct, Fin.sum_univ_three, Pi.star_apply,
        star_add, star_sub, star_mul, star_neg, star_star, map_add, map_sub, map_mul,
        map_neg, map_inv₀, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_fin_one]
      ring_nf
      norm_num [Complex.I_sq, ht]
      simp only [starRingEnd_apply] at hN ⊢
      linear_combination hN
    have hP : P = 1 - Q := by
      ext i j
      change (yMat ξ * (yMat ξ)ᴴ) i j = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j - u i * star (u j)
      fin_cases i <;> fin_cases j <;>
        norm_num [P, Q, u, t, yMat, spinOne, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
          Matrix.sub_apply, Matrix.one_apply, Pi.star_apply, star_add, star_sub, star_mul, star_star, Fin.sum_univ_three, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue] <;>
        (try decide) <;> (try ring_nf) <;>
        (try norm_num [Complex.I_sq, ht]) <;> (try ring) <;>
        (try simp only [starRingEnd_apply] at hN ⊢) <;> linear_combination hN
    have hQ : Q * Q = Q := by
      change Matrix.vecMulVec u (star u) * Matrix.vecMulVec u (star u) =
        Matrix.vecMulVec u (star u)
      rw [Matrix.vecMulVec_mul_vecMulVec, hu, one_smul]
    have hQtr : Q.trace = 1 := by
      rw [show Q = Matrix.vecMulVec u (star u) from rfl, Matrix.trace_vecMulVec,
        dotProduct_comm]
      exact hu
    have hPtr : P.trace = (2 : ℂ) := by
      rw [hP, Matrix.trace_sub, hQtr]
      norm_num
    have hP2 : P * P = P := by
      rw [hP]
      calc
        (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
        _ = 1 - Q := by rw [hQ]; abel
    have hstar : star P = P := by
      simp [P, Matrix.star_eq_conjTranspose]
    have hne : P ≠ 0 := by
      intro hzero
      rw [hzero, Matrix.trace_zero] at hPtr
      norm_num at hPtr
    have hn : ‖P‖ * ‖P‖ = ‖P‖ := by
      simpa only [hstar, hP2] using (CStarRing.norm_star_mul_self (x := P)).symm
    have hz : ‖P‖ * (‖P‖ - 1) = 0 := by nlinarith [hn]
    rcases mul_eq_zero.mp hz with h | h
    · exact False.elim ((norm_ne_zero_iff.mpr hne) h)
    · dsimp [P] at h
      linarith
  constructor
  · intro α β
    let ξ : Fin 3 → ℂ := ![(Complex.I * (Real.sin α : ℂ)) * (Real.sin β : ℂ),
      0, (Real.cos α : ℂ) + (Complex.I * (Real.sin α : ℂ)) * (Real.cos β : ℂ)]
    have htrig : (Real.sin α * Real.sin β) ^ 2 + (Real.cos α) ^ 2 +
        (Real.sin α * Real.cos β) ^ 2 = 1 := by
      calc
        _ = (Real.cos α) ^ 2 + (Real.sin α) ^ 2 *
            ((Real.sin β) ^ 2 + (Real.cos β) ^ 2) := by ring
        _ = 1 := by rw [Real.sin_sq_add_cos_sq, mul_one]; nlinarith [Real.sin_sq_add_cos_sq α]
    have hunit : WHAdditivity.Renyi.IsUnitVector ξ := by
      norm_num [-Complex.ofReal_sin, -Complex.ofReal_cos,
        WHAdditivity.Renyi.IsUnitVector, ξ, Fin.sum_univ_three,
        Complex.normSq_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_fin_one]
      nlinarith [htrig]
    have heq : yMat ξ = zMat α β := by
      simp only [yMat, zMat, ξ, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val']
      module <;> simp [Matrix.head_cons, Matrix.tail_cons]
    rw [← heq]
    exact hy ξ hunit
  · exact hy
