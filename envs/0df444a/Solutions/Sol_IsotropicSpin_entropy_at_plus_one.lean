-- Prove2me | solution 1 for IsotropicSpin.entropy_at_plus_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:12:31.091915+00:00
-- url     : https://prove2.me/submissions/9efbb214-b263-4eac-a0ba-abe4ccab32cf

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_isotropicChannel

open IsotropicSpin in
theorem solution :
    WHAdditivity.Renyi.vonNeumannEntropy
        (isotropicChannel 1 spinOne (WHAdditivity.Renyi.pureState (Pi.single 0 1 : Fin 3 → ℂ))) =
      Real.log 2 := by
  set D : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1 / 2, 1 / 2, 0] with hDdef
  have hent : ∀ (S : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3),
      (S * WHAdditivity.Renyi.pureState (Pi.single 0 1 : Fin 3 → ℂ) * S) i j = S i 0 * S 0 j := by
    intro S i j
    simp only [Matrix.mul_apply, WHAdditivity.Renyi.pureState, Matrix.vecMulVec_apply,
      Fin.sum_univ_three, Pi.star_apply]
    simp
  have hD : isotropicChannel 1 spinOne
      (WHAdditivity.Renyi.pureState (Pi.single 0 1 : Fin 3 → ℂ)) = D := by
    unfold isotropicChannel
    ext i j
    rw [Matrix.smul_apply, Matrix.sum_apply, Fin.sum_univ_three, hent, hent, hent, smul_eq_mul]
    unfold spinOne
    generalize hc : ((Real.sqrt 2)⁻¹ : ℂ) = c
    have hc2 : c ^ 2 = 1 / 2 := by
      rw [← hc, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    fin_cases i <;> fin_cases j <;>
      simp [hDdef] <;> (try ring_nf) <;> (try simp [Complex.I_sq, hc2]) <;> (try norm_num)
  rw [hD]
  unfold WHAdditivity.Renyi.vonNeumannEntropy
  have hsa : IsSelfAdjoint D := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hDdef, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    fin_cases i <;> simp
  have hspec : ∀ x ∈ spectrum ℝ D, x = 0 ∨ x = 1 / 2 := by
    intro x hx
    rw [← spectrum.algebraMap_mem_iff ℂ, hDdef, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    fin_cases i
    · right
      have : ((1 / 2 : ℝ) : ℂ) = (x : ℂ) := by simpa using hi
      exact (Complex.ofReal_injective this).symm
    · right
      have : ((1 / 2 : ℝ) : ℂ) = (x : ℂ) := by simpa using hi
      exact (Complex.ofReal_injective this).symm
    · left
      have : ((0 : ℝ) : ℂ) = (x : ℂ) := by simpa using hi
      exact (Complex.ofReal_injective this).symm
  have hcongr : cfc Real.negMulLog D = cfc (fun x => Real.log 2 * x) D := by
    apply cfc_congr
    intro x hx
    rcases hspec x hx with rfl | rfl
    · simp
    · simp only [Real.negMulLog, one_div, Real.log_inv]
      ring
  rw [hcongr, cfc_const_mul_id _ D hsa, Matrix.trace_smul]
  have htr : D.trace = 1 := by
    rw [hDdef, Matrix.trace_diagonal, Fin.sum_univ_three]
    simp
    norm_num
  rw [htr, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
