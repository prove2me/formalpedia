-- Prove2me | solution 1 for HardyFiveAxioms.bloch_D_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:22:03.162884+00:00
-- url     : https://prove2.me/submissions/574ca0a4-e06d-4214-855c-a45aa55c52fc

import Mathlib
import Definitions.Def_hardy2001_projectors

set_option autoImplicit false

namespace HardyFiveAxioms.CebaAux

open HardyFiveAxioms

lemma s_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; rfl

lemma P0 : proj (ket (0 : Fin 2)) = !![1, 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ket, Matrix.vecMulVec_apply]

lemma P1 : proj (ket (1 : Fin 2)) = !![0, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ket, Matrix.vecMulVec_apply]

lemma P2 : proj (ketX (0 : Fin 2) 1) = !![1/2, 1/2; 1/2, 1/2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj, ketX, ket, Matrix.vecMulVec_apply, Complex.conj_ofReal] <;> linear_combination s_sq

lemma P3 : proj (ketY (0 : Fin 2) 1) = !![1/2, -Complex.I/2; Complex.I/2, 1/2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj, ketY, ket, Matrix.vecMulVec_apply, Complex.conj_ofReal] <;>
    first | linear_combination s_sq | linear_combination Complex.I * s_sq | linear_combination (-Complex.I) * s_sq | linear_combination (1/2 : ℂ) * s_sq | linear_combination (Complex.I/2) * s_sq | linear_combination (-Complex.I/2) * s_sq | linear_combination (-Complex.I^2) * s_sq - (1/2:ℂ) * Complex.I_sq | linear_combination (Complex.I^2) * s_sq + (1/2:ℂ) * Complex.I_sq | (have hI := Complex.I_sq; have hs := s_sq; ring_nf; ring_nf at hs; rw [hs, hI]; ring_nf) | (simp only [mul_comm, mul_left_comm, mul_assoc, Complex.I_mul_I] at *; linear_combination (-1:ℂ) * s_sq)

end HardyFiveAxioms.CebaAux

open HardyFiveAxioms in
theorem solution :
    let P : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
      ![proj (ket 0), proj (ket 1), proj (ketX 0 1), proj (ketY 0 1)]
    ∀ i j : Fin 4, (P i * P j).trace =
      ((!![1, 0, 1 / 2, 1 / 2;
           0, 1, 1 / 2, 1 / 2;
           1 / 2, 1 / 2, 1, 1 / 2;
           1 / 2, 1 / 2, 1 / 2, 1] : Matrix (Fin 4) (Fin 4) ℝ) i j : ℂ) := by
  intro P i j
  simp only [P, HardyFiveAxioms.CebaAux.P0, HardyFiveAxioms.CebaAux.P1,
    HardyFiveAxioms.CebaAux.P2, HardyFiveAxioms.CebaAux.P3]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring_nf
