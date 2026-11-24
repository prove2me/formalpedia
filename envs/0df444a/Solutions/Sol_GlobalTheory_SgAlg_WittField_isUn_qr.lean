-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.isUn_qr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:15.952057+00:00
-- url     : https://prove2.me/submissions/4dec9fed-f48d-43e0-9da6-0065c1510e2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_of_form
import Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_form

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
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (u : Fin n → E) (l : E)
    (hl : l * σ l * form σ J u u = l + σ l) : IsUn σ J (qr σ J u l) :=
  isUn_of_form (qr_form hσ hJ u l hl)
end GlobalTheory.SgAlg.WittField
