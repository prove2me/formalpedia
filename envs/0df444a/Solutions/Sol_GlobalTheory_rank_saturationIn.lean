-- Prove2me | solution 1 for GlobalTheory.rank_saturationIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:04.018678+00:00
-- url     : https://prove2.me/submissions/29697b16-4cf5-4e50-b88b-a3be1048d927

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_rank_saturation
import Theorems.Thm_GlobalTheory_map_subtype_saturation_submoduleOf

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
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']
namespace GlobalTheory
theorem _root_.solution [IsDomain R] {M N : Submodule R V} (h : N ≤ M) :
    Module.rank R (saturationIn M N) = Module.rank R N := by
  rw [← map_subtype_saturation_submoduleOf,
    ← (Submodule.equivMapOfInjective M.subtype Subtype.coe_injective
      (saturation (N.submoduleOf M))).rank_eq, rank_saturation,
    (Submodule.submoduleOfEquivOfLe h).rank_eq]
end GlobalTheory
