-- Prove2me | solution 1 for GlobalTheory.T.exists_complete_dvr_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:41.736974+00:00
-- url     : https://prove2.me/submissions/dd075a30-7473-477d-99bc-7e47e07545ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtension
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtensionStatement
import Theorems.Thm_GlobalTheory_CompleteDVR_exists_complete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V], ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O), Function.Injective φ ∧ IsLocalHom φ := by
  first | exact @GlobalTheory.CompleteDVR.exists_complete | exact GlobalTheory.CompleteDVR.exists_complete | (intros; apply GlobalTheory.CompleteDVR.exists_complete <;> assumption)
end _root_.GlobalTheory.T
