-- Prove2me | solution 1 for GlobalTheory.rank_normal_form_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:40.146519+00:00
-- url     : https://prove2.me/submissions/154e7fbd-98e0-442e-b482-410083ee9457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankNormalFormMatrixField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  intro k _ n C
  classical
  obtain ⟨L, L', d, hd⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal C
  refine ⟨Matrix.diagonal (fun i => if d i = 0 then 1 else (d i)⁻¹) * (L.map Matrix.TransvectionStruct.toMatrix).prod,
    (L'.map Matrix.TransvectionStruct.toMatrix).prod, fun i => if d i = 0 then 0 else 1, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, mul_one, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero
  · intro i; by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ C, hd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : d i = 0 <;> simp [h]
end GlobalTheory
