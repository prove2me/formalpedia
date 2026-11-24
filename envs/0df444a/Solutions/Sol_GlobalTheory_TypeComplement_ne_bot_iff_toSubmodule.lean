-- Prove2me | solution 1 for GlobalTheory.TypeComplement.ne_bot_iff_toSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:28.987802+00:00
-- url     : https://prove2.me/submissions/536993fb-d736-4636-8aa3-a09414f6e424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
namespace GlobalTheory.TypeComplement
theorem _root_.solution {S : Subrepresentation ρ} : S ≠ ⊥ ↔ S.toSubmodule ≠ ⊥ := by
  constructor
  · intro h h'
    exact h (Subrepresentation.toSubmodule_injective h')
  · rintro h rfl
    exact h rfl
end GlobalTheory.TypeComplement
