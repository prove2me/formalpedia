-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.isUn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:59:52.464308+00:00
-- url     : https://prove2.me/submissions/bab96cd0-d5a5-4a29-95a2-5a7d8f19072c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_cT_mul

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
theorem _root_.solution {g h : Matrix (Fin n) (Fin n) E} (hg : IsUn σ J g) (hh : IsUn σ J h) :
    IsUn σ J (g * h) := by
  unfold IsUn at *
  have : cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h := by
    simp only [Matrix.mul_assoc]
  rw [cT_mul, this, hg, hh]
end GlobalTheory.SgAlg.WittField
