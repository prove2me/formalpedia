-- Prove2me | solution 1 for GlobalTheory.UnRep.WeakApprox.exists_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:05.445205+00:00
-- url     : https://prove2.me/submissions/28098bb1-a6a5-4b44-986c-6553d906cb34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes

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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (Λ : AddSubgroup (Fin n → R))
    (M : Matrix (Fin n) (Fin n) R) (D : ℕ) (hD : IsUnit (D : R))
    (h : ∀ z ∈ Λ, ∃ w ∈ Λ, M *ᵥ z = D • w) : ∃ X ∈ stab Λ, M = D • X := by
  obtain ⟨u, hu⟩ := hD.exists_left_inv
  refine ⟨u • M, fun z hz => ?_, ?_⟩
  · obtain ⟨w, hw, e⟩ := h z hz
    rwa [Matrix.smul_mulVec, e, ← Nat.cast_smul_eq_nsmul R, smul_smul, hu, one_smul]
  · rw [← Nat.cast_smul_eq_nsmul R, smul_smul, mul_comm, hu, one_smul]
end GlobalTheory.UnRep.WeakApprox
