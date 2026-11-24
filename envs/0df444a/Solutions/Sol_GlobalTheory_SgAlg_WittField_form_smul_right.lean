-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.form_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:42.043349+00:00
-- url     : https://prove2.me/submissions/0bf8e7a9-3dcb-491c-b02d-3b1196a39068

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
theorem _root_.solution (c : E) (v w : Fin n → E) : form σ J v (c • w) = σ c * form σ J v w := by
  simp only [form, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => σ c * σ (w i)) = σ c • (fun i => σ (w i)) from rfl, smul_dotProduct, smul_eq_mul]
end GlobalTheory.SgAlg.WittField
