-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.sup_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:49.899796+00:00
-- url     : https://prove2.me/submissions/62ff73b0-0a0f-4e0c-9866-f4377358daf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_LengthCommensurable_inf_right
import Theorems.Thm_GlobalTheory_LengthCommensurable_sup_left

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
theorem _root_.solution (h : LengthCommensurable A B) : LengthCommensurable (A ⊔ B) (A ⊓ B) :=
  ((refl A).sup_left h.symm).inf_right (h.sup_left (refl B))
end GlobalTheory.LengthCommensurable
