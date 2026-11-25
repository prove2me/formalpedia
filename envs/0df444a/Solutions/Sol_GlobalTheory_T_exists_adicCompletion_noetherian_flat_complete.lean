-- Prove2me | solution 1 for GlobalTheory.T.exists_adicCompletion_noetherian_flat_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:17:52.166524+00:00
-- url     : https://prove2.me/submissions/4cf34b70-24b0-409f-ab85-059d91637674

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdicCompletionNoetherianFlatComplete
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdicCompletionNoetherianFlatCompleteStatement
import Theorems.Thm_GlobalTheory_AdicPackage_adicCompletion_package


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
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B), ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧ IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  first | exact @GlobalTheory.AdicPackage.adicCompletion_package | exact GlobalTheory.AdicPackage.adicCompletion_package | (intros; apply GlobalTheory.AdicPackage.adicCompletion_package <;> assumption)
end _root_.GlobalTheory.T
