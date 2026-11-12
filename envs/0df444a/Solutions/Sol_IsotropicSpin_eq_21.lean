-- Prove2me | solution 1 for IsotropicSpin.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T21:09:33.603332+00:00
-- url     : https://prove2.me/submissions/9bc43056-e777-4abf-8625-1fc5d18229bf

import Mathlib
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_zMat

open scoped Matrix
open IsotropicSpin


/-- **`ZZ†` and its eigenvalue `1`**, Alicki, arXiv:quant-ph/0402080v1, eqs. (20)–(21), pp. 2–3.
For real `α, β` put `a = cos α`, `b = sin α cos β`, `c = (1/√2) sin α sin β` (20). Then

1. `a² + b² + 2c² = 1` (20);
2. `Z Z† = !![a²+b²+c², −ic(a+ib), c²; ic(a−ib), 2c², −ic(a−ib); c², ic(a+ib), a²+b²+c²]`, the
   matrix whose characteristic polynomial `W(λ)` is the first determinant of (21);
3. `λ = 1` is an eigenvalue of `Z Z†`: `W(1) = det(Z Z† − 𝟙) = 0`.

**Formalization Note** `1/√2` is `(√2)⁻¹`. `Matrix.charpoly` is `det(λ𝟙 − M)`, which vanishes at
the same `λ` as the page's `W(λ) = det(M − λ𝟙)`. -/
theorem solution (α β : ℝ) :
    (Real.cos α) ^ 2 + (Real.sin α * Real.cos β) ^ 2 +
        2 * ((Real.sqrt 2)⁻¹ * Real.sin α * Real.sin β) ^ 2 = 1 ∧
    zMat α β * (zMat α β)ᴴ =
      (let a : ℂ := Real.cos α
       let b : ℂ := Real.sin α * Real.cos β
       let c : ℂ := (Real.sqrt 2)⁻¹ * Real.sin α * Real.sin β
       !![a ^ 2 + b ^ 2 + c ^ 2, -Complex.I * c * (a + Complex.I * b), c ^ 2;
          Complex.I * c * (a - Complex.I * b), 2 * c ^ 2, -Complex.I * c * (a - Complex.I * b);
          c ^ 2, Complex.I * c * (a + Complex.I * b), a ^ 2 + b ^ 2 + c ^ 2]) ∧
    (zMat α β * (zMat α β)ᴴ).charpoly.eval 1 = 0 := by
  classical
  have hs : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hn : (Real.cos α) ^ 2 + (Real.sin α * Real.cos β) ^ 2 +
      2 * ((Real.sqrt 2)⁻¹ * Real.sin α * Real.sin β) ^ 2 = 1 := by
    calc
      _ = (Real.cos α) ^ 2 + (Real.sin α) ^ 2 *
          ((Real.cos β) ^ 2 + (Real.sin β) ^ 2) := by
        calc
          _ = (Real.cos α) ^ 2 + (Real.sin α) ^ 2 * (Real.cos β) ^ 2 +
              2 * ((Real.sqrt 2)⁻¹ ^ 2) * (Real.sin α) ^ 2 * (Real.sin β) ^ 2 := by ring
          _ = _ := by rw [hs]; ring
      _ = 1 := by
        rw [add_comm ((Real.cos β) ^ 2) ((Real.sin β) ^ 2),
          Real.sin_sq_add_cos_sq, mul_one]
        nlinarith [Real.sin_sq_add_cos_sq α]
  let a : ℂ := Real.cos α
  let b : ℂ := Real.sin α * Real.cos β
  let c : ℂ := (Real.sqrt 2)⁻¹ * Real.sin α * Real.sin β
  let A : Matrix (Fin 3) (Fin 3) ℂ :=
    !![a ^ 2 + b ^ 2 + c ^ 2, -Complex.I * c * (a + Complex.I * b), c ^ 2;
       Complex.I * c * (a - Complex.I * b), 2 * c ^ 2, -Complex.I * c * (a - Complex.I * b);
       c ^ 2, Complex.I * c * (a + Complex.I * b), a ^ 2 + b ^ 2 + c ^ 2]
  have hnC : a ^ 2 + b ^ 2 + 2 * c ^ 2 = (1 : ℂ) := by
    dsimp [a, b, c]
    exact_mod_cast hn
  have hm : zMat α β * (zMat α β)ᴴ = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [-Complex.ofReal_sin, -Complex.ofReal_cos, A, a, b, c, zMat, spinOne, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_three,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue] <;>
      (try simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos,
        starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]) <;>
      (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> (try ring)
  refine ⟨hn, hm, ?_⟩
  rw [hm, Matrix.eval_charpoly]
  have hAv : A *ᵥ (![1, 0, 1] : Fin 3 → ℂ) = ![1, 0, 1] := by
    ext i
    fin_cases i <;>
      norm_num [-Complex.ofReal_sin, -Complex.ofReal_cos, A, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one,
        Matrix.of_apply, Fin.isValue] <;>
      (try decide) <;> (try ring) <;> linear_combination hnC
  have hk : (1 - A) *ᵥ (![1, 0, 1] : Fin 3 → ℂ) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hAv, sub_self]
  have hd : (1 - A).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hk
      (i := (0 : Fin 3)) (by simp)
  simpa only [map_one] using hd
