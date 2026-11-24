-- Prove2me | solution 1 for GlobalTheory.UnRep.WeakApprox.skewPart_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:42:34.241278+00:00
-- url     : https://prove2.me/submissions/52b870b4-e310-41de-8120-8234cb6b4be1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
import Theorems.Thm_P2M_GlobalTheory_UnRep_WeakApprox_map_smul___9facef897ec7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.WeakApprox
namespace GlobalTheory.UnRep.WeakApprox
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G : Matrix (Fin n) (Fin n) R)
    (a : R) (ha : σ a = a) (A : Matrix (Fin n) (Fin n) R) :
    skewPart σ G (a • A) = a • skewPart σ G A := by
  change a • A - (G * (a • A).map σ * G⁻¹)ᵀ = a • (A - (G * A.map σ * G⁻¹)ᵀ)
  rw [map_smul'', ha, mul_smul_comm, smul_mul_assoc, Matrix.transpose_smul, smul_sub]
end GlobalTheory.UnRep.WeakApprox
