-- Prove2me | solution 1 for N25.jAnalytic_middle_ratio_limit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:01.589781+00:00
-- url     : https://prove2.me/submissions/69b27d04-9dc6-4cdd-84ce-b2113d63448d

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_N25_matrix_det25_triangular
import Theorems.Thm_N25_dilation25_triangular_action
import Theorems.Thm_N25_dilation25_triangular_middle
import Theorems.Thm_N25_jAnalytic_sl_invariant
import Theorems.Thm_N25_jAnalytic_shift_ratio_limit
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false

open Filter Topology UpperHalfPlane Matrix

open scoped MatrixGroups

namespace N25

/-- Every width-five matrix direction has the nontrivial fifth-root j-ratio limit. -/
theorem _root_.solution (A : SL(2, ℤ))
    (hA5 : (5 : ℤ) ∣ A 1 0) (hA25 : ¬ (25 : ℤ) ∣ A 1 0) :
    ∃ v : ℤ, ¬ (5 : ℤ) ∣ v ∧
      Tendsto (fun τ : UpperHalfPlane =>
        (ModularForm.E₄ (ModularForm.heckeDiagMatrix 25 • (A • τ)) ^ 3 /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix 25 • (A • τ))) /
        (ModularForm.E₄ (A • τ) ^ 3 / ModularForm.discriminant (A • τ)))
        UpperHalfPlane.atImInfty
        (nhds (Complex.exp (-(2 * Real.pi * Complex.I * ((v : ℂ) / 5))))) := by
  have hdet : (!![(25 : ℤ), 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) ℤ)).det = 25 := by
    rw [Matrix.det_mul, A.property]
    norm_num [Matrix.det_fin_two]
  obtain ⟨B, d, e, v, _, hd, he, hde, hm⟩ :=
    N25.matrix_det25_triangular _ hdet
  obtain ⟨hd5, he5, hv⟩ := dilation25_triangular_middle A B d e v he hde hm hA5 hA25
  rw [hd5, he5] at hm
  have hh (τ : UpperHalfPlane) := N25.dilation25_triangular_action A B 5 5 v
    (by norm_num) (by norm_num) hm τ
  choose φ hφ hBφ using hh
  have hφ' (τ : UpperHalfPlane) : (φ τ : ℂ) = (τ : ℂ) + (((v : ℝ) / 5 : ℝ) : ℂ) := by
    rw [hφ]
    push_cast
    ring
  have harg (τ : UpperHalfPlane) : B • φ τ = ModularForm.heckeDiagMatrix 25 • (A • τ) := by
    apply UpperHalfPlane.ext
    rw [ModularForm.coe_heckeDiagMatrix_smul (by norm_num : (25 : ℕ) ≠ 0)]
    simpa using hBφ τ
  refine ⟨v, hv, ?_⟩
  have ht := jAnalytic_shift_ratio_limit ((v : ℝ) / 5) φ hφ'
  have heq (τ : UpperHalfPlane) :
      (ModularForm.E₄ (ModularForm.heckeDiagMatrix 25 • (A • τ)) ^ 3 /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix 25 • (A • τ))) /
        (ModularForm.E₄ (A • τ) ^ 3 / ModularForm.discriminant (A • τ)) =
      (ModularForm.E₄ (φ τ) ^ 3 / ModularForm.discriminant (φ τ)) /
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) := by
    rw [← harg, jAnalytic_sl_invariant, jAnalytic_sl_invariant]
  simpa only [heq, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat] using ht

end N25
