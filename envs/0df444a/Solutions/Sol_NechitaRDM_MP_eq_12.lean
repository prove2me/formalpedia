-- Prove2me | solution 1 for NechitaRDM.MP.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:57:08.325079+00:00
-- url     : https://prove2.me/submissions/a4b6f1b5-c9d5-4e01-b9c3-78dc55da5348

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

open NechitaRDM.MP

theorem solution {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ) :
    WildeQIT.partialTraceRight (pureState fun p : Fin n × Fin k => X p.1 p.2) =
      (wishart X).trace⁻¹ • wishart X := by
  have htr : (((∑ p : Fin n × Fin k, ‖X p.1 p.2‖ ^ 2 : ℝ)) : ℂ) = (wishart X).trace := by
    simp only [wishart, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  ext i j
  simp only [WildeQIT.partialTraceRight, pureState, Matrix.of_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, wishart, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [htr, ← Finset.mul_sum]
  simp only [wishart]
