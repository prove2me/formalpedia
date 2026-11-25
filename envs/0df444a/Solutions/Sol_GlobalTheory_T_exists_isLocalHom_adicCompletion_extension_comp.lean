-- Prove2me | solution 1 for GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:51.123287+00:00
-- url     : https://prove2.me/submissions/394ad946-7acb-4a8e-92e1-9c3ee8f36a70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalHomAdicCompletionExtend
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalHomAdicCompletionExtendStatement
import Theorems.Thm_GlobalTheory_LocalCompletion_exists_localHom_adicCompletion_extend


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ → ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R, IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  first | exact @GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | exact GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend | (intros; apply GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend <;> assumption)
end _root_.GlobalTheory.T
