-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.qr_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:18.422376+00:00
-- url     : https://prove2.me/submissions/a0e7c039-d02c-4cf3-8445-330db193a7e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittField
variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.SgAlg.WittField
theorem _root_.solution (u : Fin n → E) (l : E) (v : Fin n → E) :
    qr σ J u l *ᵥ v = v - (l * form σ J v u) • u := by
  have h1 : ((fun i => σ (u i)) ᵥ* J) ⬝ᵥ v = form σ J v u := by
    unfold form; rw [dotProduct_mulVec]
  unfold qr
  rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, h1, op_smul_eq_smul, smul_smul]
end GlobalTheory.SgAlg.WittField
