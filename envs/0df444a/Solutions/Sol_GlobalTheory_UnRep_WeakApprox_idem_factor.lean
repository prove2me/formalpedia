-- Prove2me | solution 1 for GlobalTheory.UnRep.WeakApprox.idem_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:40:45.917143+00:00
-- url     : https://prove2.me/submissions/76bb9995-5ea2-4943-b0ed-fc2e33810529

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
theorem _root_.solution {R M : Type} [CommRing R] [Ring M] [Algebra R M] (e : R) (he : e * e = e)
    (S T U : M) (hU : U * (1 + S) = 1) :
    e • (1 + T) = e • ((1 + e • (-((S - T) * U))) * (1 + S)) := by
  have : (1 + e • (-((S - T) * U))) * (1 + S) = (1 + S) - e • (S - T) := by
    rw [add_mul, one_mul, smul_mul_assoc, neg_mul, mul_assoc, hU, mul_one, smul_neg, sub_eq_add_neg (1 + S)]
  rw [this, smul_sub e (1 + S), smul_smul, he, ← smul_sub]
  congr 1
  abel
end GlobalTheory.UnRep.WeakApprox
