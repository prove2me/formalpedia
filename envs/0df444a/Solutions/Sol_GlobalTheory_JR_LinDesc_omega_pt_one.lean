-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.omega_pt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:18.113805+00:00
-- url     : https://prove2.me/submissions/051f623b-369a-4289-9b8b-b95a8fc09459

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorLinearDescentPointOne
import Theorems.Thm_GlobalTheory_JR_LinDesc_eta_inv_eq
import Theorems.Thm_GlobalTheory_JR_LinDesc_eta_neg_one_pow
import Theorems.Thm_GlobalTheory_JR_LinDesc_Cm_pt_one
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_jacquetRallis_transfer_factor_krylov_det
import Theorems.Thm_GlobalTheory_T_unramifiedValuationParitySign_character_kernel_norms


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F),
    ∃ κ₀ : ℂ, ∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F,
      omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a := by
  intro F E _ _ _ _ _ A r τ p hG lam
  obtain ⟨hmul, -, -, -⟩ := GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E
  have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have hT : (Algebra.traceMatrix F (bas A hG)).det ≠ 0 := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (bas A hG)] at hnd
    convert hnd using 2
    ext i j
    rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  refine ⟨eta (Algebra.traceMatrix F (bas A hG)).det, fun a ha g => ?_⟩
  have hL := GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det F r
  have hdet : (g : Matrix (Fin r) (Fin r) F).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hg : (g : Matrix (Fin r) (Fin r) F).det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hginv := eq_inv_of_mul_eq_one_right hdet
  have hna : Algebra.norm F a ≠ 0 := (ha.map (Algebra.norm F)).ne_zero
  have hr : (-1 : F) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  unfold omega Et.etaK
  rw [hL.1, hL.2, Cm_pt_one, Matrix.det_mul, Matrix.det_mul, ← Algebra.norm_eq_matrix_det, hginv,
    hmul _ _ hr (mul_ne_zero (mul_ne_zero hT hna) (inv_ne_zero hg)),
    hmul _ _ (mul_ne_zero hT hna) (inv_ne_zero hg), hmul _ _ hT hna, eta_neg_one_pow, eta_inv_eq]
  ring
end GlobalTheory.JR.LinDesc
