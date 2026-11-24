-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.single_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:45:38.575198+00:00
-- url     : https://prove2.me/submissions/a23d3fe5-0eb1-4c44-b754-1947c18cb61a

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (fun k => σ ((Pi.single i (1 : E) : Fin n → E) k)) ⬝ᵥ (M *ᵥ (Pi.single j (1 : E) : Fin n → E)) = M i j := by
  have : (fun k => σ ((Pi.single i (1 : E) : Fin n → E) k)) = (Pi.single i (1 : E) : Fin n → E) := by
    funext k; by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [this]
  simp [mulVec, dotProduct, Pi.single_apply]
end GlobalTheory.SgAlg.WittField
