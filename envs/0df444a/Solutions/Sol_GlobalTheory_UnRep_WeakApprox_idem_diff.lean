-- Prove2me | solution 1 for GlobalTheory.UnRep.WeakApprox.idem_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:06.313186+00:00
-- url     : https://prove2.me/submissions/badec32c-ebbb-4777-a622-2f614f2f0bf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
import Theorems.Thm_GlobalTheory_UnRep_WeakApprox_idem_factor
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
theorem _root_.solution {R M : Type} [CommRing R] [Ring M] [Algebra R M] (e : R) (he : e * e = e)
    (S T U V W : M) (hU : U * (1 + S) = 1) (hU' : (1 + S) * U = 1) (hV : V * (1 + T) = 1)
    (hV' : (1 + T) * V = 1) (hW : W * (1 + e • (-((S - T) * U))) = 1) :
    e • (V - U) = e • (U * W * (S - T) * U) := by
  have h1 : V - U = V * (S - T) * U := by
    have : S - T = (1 + S) - (1 + T) := by abel
    rw [this, mul_sub, sub_mul, mul_assoc V, hU', hV, mul_one, one_mul]
  have h2 : e • (U * W) = e • V := by
    calc e • (U * W) = U * W * (e • (1 + T)) * V := by
          rw [mul_smul_comm, smul_mul_assoc, mul_assoc (U * W), hV', mul_one]
      _ = e • (U * (W * (1 + e • (-((S - T) * U)))) * (1 + S) * V) := by
          rw [idem_factor e he S T U hU, mul_smul_comm, smul_mul_assoc]
          simp only [mul_assoc]
      _ = e • V := by rw [hW, mul_one, hU, one_mul]
  rw [h1, ← smul_mul_assoc, ← smul_mul_assoc, ← h2, smul_mul_assoc, smul_mul_assoc]
end GlobalTheory.UnRep.WeakApprox
