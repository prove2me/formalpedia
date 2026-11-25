-- Prove2me | solution 1 for GlobalTheory.T.exists_regular_completion_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:16:15.222879+00:00
-- url     : https://prove2.me/submissions/d0b7d9bd-199c-45e4-90c1-d5f13e4423c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularCompletionFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularCompletionFlatStatement
import Theorems.Thm_GlobalTheory_RegularCompletionPackage_exists_regular_completion


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
theorem _root_.solution : ∀ (R₁ Ω : Type) [CommRing R₁] [IsRegularLocalRing R₁] [Field Ω] (u : R₁ →+* Ω), RingHom.ker u = maximalIdeal R₁ → ∃ (C : Type) (_ : CommRing C) (_ : IsRegularLocalRing C) (c : R₁ →+* C) (uC : C →+* Ω), c.Flat ∧ (maximalIdeal R₁).map c = maximalIdeal C ∧ IsAdicComplete (maximalIdeal C) C ∧ RingHom.ker uC = maximalIdeal C ∧ uC.comp c = u := by
  first | exact @GlobalTheory.RegularCompletionPackage.exists_regular_completion | exact GlobalTheory.RegularCompletionPackage.exists_regular_completion | (intros; apply GlobalTheory.RegularCompletionPackage.exists_regular_completion <;> assumption)
end _root_.GlobalTheory.T
