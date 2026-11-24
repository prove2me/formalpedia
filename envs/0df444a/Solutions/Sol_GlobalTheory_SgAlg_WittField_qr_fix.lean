-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.qr_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:56.051461+00:00
-- url     : https://prove2.me/submissions/a7cf725d-53ca-417d-89c9-956753494414

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_mulVec

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
theorem _root_.solution (u : Fin n → E) (l : E) (y : Fin n → E) (hy : form σ J y u = 0) :
    qr σ J u l *ᵥ y = y := by
  rw [qr_mulVec, hy]; simp
end GlobalTheory.SgAlg.WittField
