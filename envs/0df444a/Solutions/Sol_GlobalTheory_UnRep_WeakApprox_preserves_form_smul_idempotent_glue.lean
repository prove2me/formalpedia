-- Prove2me | solution 1 for GlobalTheory.UnRep.WeakApprox.preserves_form_smul_idempotent_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:07.244578+00:00
-- url     : https://prove2.me/submissions/87fe610d-c9a9-4166-a407-5e645b689650

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
import Theorems.Thm_P2M_GlobalTheory_UnRep_WeakApprox_map_smul___9facef897ec7
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.WeakApprox
namespace GlobalTheory.UnRep.WeakApprox
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G h : Matrix (Fin n) (Fin n) R)
    (e l : R) (he : e * e = e) (hσ : σ e = e) (hl : l * σ l = 1) (hh : hᵀ * G * h.map σ = G) :
    (l • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)))ᵀ * G *
      (l • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R))).map σ = G := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, h0', mul_one, sub_zero]
  rw [map_smul'', Matrix.map_add _ (map_add σ), map_smul'', map_smul'',
    Matrix.map_one _ (map_zero σ) (map_one σ), map_sub, map_one, hσ, Matrix.transpose_smul,
    Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
    smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hl, one_smul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, he, h0, h0', h1, hh,
    zero_smul, one_mul, mul_one, add_zero, zero_add]
  rw [← add_smul]
  simp
end GlobalTheory.UnRep.WeakApprox
