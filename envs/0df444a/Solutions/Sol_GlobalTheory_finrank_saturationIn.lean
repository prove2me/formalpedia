-- Prove2me | solution 1 for GlobalTheory.finrank_saturationIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:19.922295+00:00
-- url     : https://prove2.me/submissions/b9282dd5-54bf-4c4e-abdc-134134145396

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_rank_saturationIn

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
theorem _root_.solution [IsDomain R] {M N : Submodule R V} [Module.Finite R M] (h : N ≤ M) :
    Module.finrank R (saturationIn M N) = Module.finrank R N := congrArg Cardinal.toNat (rank_saturationIn h)
end GlobalTheory
