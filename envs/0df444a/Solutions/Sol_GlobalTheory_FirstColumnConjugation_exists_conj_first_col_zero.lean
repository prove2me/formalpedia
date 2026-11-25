-- Prove2me | solution 1 for GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:59.414055+00:00
-- url     : https://prove2.me/submissions/76f748ac-071a-4f81-b963-2966ff652114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDetNeZeroFirstCol
import Theorems.Thm_GlobalTheory_FirstColumnConjugation_exists_det_ne_zero_first_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FirstColumnConjugation
open Matrix
namespace GlobalTheory.FirstColumnConjugation
theorem _root_.solution {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      Matrix.det P ≠ 0 ∧ (∀ a : Fin n, B (Fin.succ a) 0 = 0) ∧ A * P = P * B := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.1 hv.1
    rwa [Matrix.toLin'_apply] at h
  obtain ⟨P, hP, hPv⟩ := exists_det_ne_zero_first_col v hv.2
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (Ne.isUnit hP)
  refine ⟨P, P⁻¹ * A * P, hP, fun a => ?_, ?_⟩
  · have hPe : P *ᵥ Pi.single 0 1 = v := by
      ext k
      rw [mulVec_single_one]
      exact hPv k
    have hcol : (P⁻¹ * A * P) *ᵥ Pi.single 0 1 = μ • Pi.single 0 1 := by
      rw [← mulVec_mulVec, hPe, ← mulVec_mulVec, hAv, mulVec_smul, ← hPe, mulVec_mulVec,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).1 hu), one_mulVec]
    have h := congrFun hcol (Fin.succ a)
    rw [mulVec_single_one] at h
    simpa [Pi.single_apply, Fin.succ_ne_zero] using h
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).1 hu),
      Matrix.one_mul]
end GlobalTheory.FirstColumnConjugation
