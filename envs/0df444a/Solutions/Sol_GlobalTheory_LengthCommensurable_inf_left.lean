-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.inf_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:55.442134+00:00
-- url     : https://prove2.me/submissions/5ca9b766-408a-4a4a-a08a-b03031830f3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_LengthCommensurable_inf_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable {A A' B B' C : Submodule R V}
open GlobalTheory.LengthCommensurable
namespace GlobalTheory.LengthCommensurable
theorem _root_.solution (hAC : LengthCommensurable A C) (hBC : LengthCommensurable B C) :
    LengthCommensurable (A ⊓ B) C :=
  (hAC.symm.inf_right hBC.symm).symm
end GlobalTheory.LengthCommensurable
