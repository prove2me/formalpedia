-- Prove2me | solution 1 for GlobalTheory.FockDetDer.hasDerivAt_det_one_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:26:55.326299+00:00
-- url     : https://prove2.me/submissions/de1d98bf-9de3-4862-83d5-af7a0f52e60d

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SymmetricBlockTraceInverseEqTwoMul
import Theorems.Thm_GlobalTheory_FockDetDer_symmetric_block_trace_inverse_eq_two_mul
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_hasDerivAt_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.FockDetDer
namespace GlobalTheory.FockDetDer
theorem _root_.solution : ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (t : ℝ), IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det → let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 Aᴴᵀ Aᴴ 0; let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0; IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧ HasDerivAt (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det) (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) * (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det) t := by
  intro P Q A B t h S T
  obtain ⟨h1, h2⟩ := symmetric_block_trace_inverse_eq_two_mul Aᴴ B ((t : ℂ) ^ 2) h
  refine ⟨h1, ?_⟩
  have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ)) t := by
    have := (hasDerivAt_pow 2 (t : ℂ)).comp_ofReal
    simpa using this
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun s : ℝ => 1 - ((s : ℂ) ^ 2) • (Aᴴ * B))
    (-((2 * (t : ℂ)) • (Aᴴ * B))) t (fun i j => by
      have := (hsq.mul_const ((Aᴴ * B) i j)).const_sub ((1 : Matrix (Fin Q) (Fin Q) ℂ) i j)
      simpa using this)
  refine hd.congr_deriv ?_
  have hne := h.ne_zero
  have hadj : (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).adjugate =
      (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det • (1 - ((t : ℂ) ^ 2) • (Aᴴ * B))⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hne, one_smul]
  simp only [S, T]
  rw [h2, hadj, Matrix.smul_mul, Matrix.mul_neg, Matrix.mul_smul, trace_smul, trace_neg, trace_smul]
  simp only [smul_eq_mul]
  ring
end GlobalTheory.FockDetDer
