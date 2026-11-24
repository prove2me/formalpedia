-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:10:21.957099+00:00
-- url     : https://prove2.me/submissions/cc1fc34b-6202-4739-836c-92556c22d462

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
namespace GlobalTheory
theorem _root_.solution [IsDomain R] :
    IsSaturatedSubmodule (⊥ : Submodule R M) ↔ Module.IsTorsionFree R M := by
  unfold IsSaturatedSubmodule
  rw [saturation_bot, Submodule.isTorsionFree_iff_torsion_eq_bot]
end GlobalTheory
