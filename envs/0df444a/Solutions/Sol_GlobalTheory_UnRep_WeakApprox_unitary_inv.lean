-- Prove2me | solution 1 for GlobalTheory.UnRep.WeakApprox.unitary_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:44:48.637797+00:00
-- url     : https://prove2.me/submissions/b11057b7-9cf2-4379-bf39-1c9100d8d3d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
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
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G g h : Matrix (Fin n) (Fin n) R)
    (hgh : g * h = 1) (hg : gᵀ * G * g.map σ = G) : hᵀ * G * h.map σ = G := by
  calc hᵀ * G * h.map σ = hᵀ * (gᵀ * G * g.map σ) * h.map σ := by rw [hg]
    _ = (g * h)ᵀ * G * (g * h).map σ := by
      rw [Matrix.transpose_mul, Matrix.map_mul]
      simp only [mul_assoc]
    _ = G := by rw [hgh, Matrix.map_one _ (map_zero σ) (map_one σ)]; simp
end GlobalTheory.UnRep.WeakApprox
