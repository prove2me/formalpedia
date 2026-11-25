-- Prove2me | solution 1 for GlobalTheory.IsSaturatedSubmodule.free_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:51.264029+00:00
-- url     : https://prove2.me/submissions/8578c280-4a6f-45e7-9151-ec85eac35b81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR
import Theorems.Thm_GlobalTheory_free_of_finite_of_isTorsionFree_of_valuationRing
import Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_finite_of_valuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
namespace IsSaturatedSubmodule
theorem _root_.solution [Module.Finite R M] [Module.IsTorsionFree R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R N :=
  haveI := h.finite_of_valuationRing
  free_of_finite_of_isTorsionFree_of_valuationRing R N
end IsSaturatedSubmodule
end GlobalTheory
