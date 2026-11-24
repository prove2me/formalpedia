-- Prove2me | solution 1 for GlobalTheory.pairM_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:19.417882+00:00
-- url     : https://prove2.me/submissions/b265fae5-d688-4d02-a7c3-09d101157197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {a b : Type} [Fintype a]
    (e : b ≃ a) (J : Matrix (Fin n) (Fin n) E) (X X' : Matrix (Fin n) a E) :
    pairM σ J (X'.submatrix id e) (X.submatrix id e) = (pairM σ J X' X).submatrix e e := by
  ext i j
  simp [pairM, cT, Matrix.mul_apply]
end GlobalTheory
