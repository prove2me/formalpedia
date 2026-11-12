-- Prove2me | solution 1 for IsotropicSpin.spectrum_half
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T20:45:44.093413+00:00
-- url     : https://prove2.me/submissions/51935bb4-3018-450c-8eae-66b3b9788629

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinHalf
import Definitions.Def_IsotropicSpin_isotropicChannel

open Polynomial
open IsotropicSpin


/-- **Every pure-input output of `Λ_{1/2}` has spectrum `(1/3, 2/3)`**, Alicki,
arXiv:quant-ph/0402080v1, §2, Case s = 1/2, p. 2 (sentence after (12)): "all density matrices
`Λ_{1/2}(|φ⟩⟨φ|)` possess the same spectrum `(1/3, 2/3)`".

**Formalization Note** The spectrum with multiplicities is stated basis-free through the
characteristic polynomial: `det(λ𝟙 − Λ_{1/2}(|φ⟩⟨φ|)) = (λ − 1/3)(λ − 2/3)` for every unit vector
`φ ∈ ℂ²`. `pureState φ = |φ⟩⟨φ|` and `IsUnitVector` are from the published bundle
`WHAdditivity.Renyi`. -/
theorem solution (φ : Fin 2 → ℂ) (hφ : WHAdditivity.Renyi.IsUnitVector φ) :
    (isotropicChannel (1 / 2) spinHalf (WHAdditivity.Renyi.pureState φ)).charpoly =
      (X - C (1 / 3 : ℂ)) * (X - C (2 / 3 : ℂ)) := by
  classical
  have hc (X : Matrix (Fin 2) (Fin 2) ℂ) :
      isotropicChannel (1 / 2) spinHalf X =
        (2 / 3 : ℂ) • (X.trace • (1 : Matrix (Fin 2) (Fin 2) ℂ)) - (1 / 3 : ℂ) • X := by
    have hs : (((1 / 2 : ℝ) * (1 / 2 + 1))⁻¹ : ℝ) = 4 / 3 := by norm_num
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [isotropicChannel, spinHalf, hs, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Matrix.trace_fin_two, Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue] <;>
      (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> (try ring)
  have hu : φ 0 * star (φ 0) + φ 1 * star (φ 1) = (1 : ℂ) := by
    have h : Complex.normSq (φ 0) + Complex.normSq (φ 1) = 1 := by
      simpa only [WHAdditivity.Renyi.IsUnitVector, Fin.sum_univ_two] using hφ
    simpa only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_add,
      Complex.ofReal_one] using congrArg (fun x : ℝ => (x : ℂ)) h
  have ht : (WHAdditivity.Renyi.pureState φ).trace = 1 := by
    simpa only [WHAdditivity.Renyi.pureState, Matrix.trace_fin_two,
      Matrix.vecMulVec_apply, Pi.star_apply] using hu
  have htr : (isotropicChannel (1 / 2) spinHalf
      (WHAdditivity.Renyi.pureState φ)).trace = 1 := by
    rw [hc, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_smul, ht]
    norm_num
  have hd : (isotropicChannel (1 / 2) spinHalf
      (WHAdditivity.Renyi.pureState φ)).det = (2 / 9 : ℂ) := by
    rw [hc, ht]
    simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply,
      WHAdditivity.Renyi.pureState, Matrix.vecMulVec_apply, Pi.star_apply,
      Matrix.one_apply, smul_eq_mul]
    norm_num
    change φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) = 1 at hu
    linear_combination -(2 / 9 : ℂ) * hu
  rw [Matrix.charpoly_fin_two, htr, hd]
  have hs : C (1 / 3 : ℂ) + C (2 / 3 : ℂ) = (1 : Polynomial ℂ) := by
    rw [← Polynomial.C_add]
    norm_num
  have hp : C (1 / 3 : ℂ) * C (2 / 3 : ℂ) = C (2 / 9 : ℂ) := by
    rw [← Polynomial.C_mul]
    norm_num
  calc
    X ^ 2 - C (1 : ℂ) * X + C (2 / 9 : ℂ) =
        X ^ 2 - (C (1 / 3 : ℂ) + C (2 / 3 : ℂ)) * X +
          C (1 / 3 : ℂ) * C (2 / 3 : ℂ) := by rw [hs, hp]; norm_num
    _ = _ := by ring



