-- Prove2me | solution 1 for GlobalTheory.IsSaturatedSubmodule.free_quotient_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:54:02.532952+00:00
-- url     : https://prove2.me/submissions/a1606261-f1e5-476c-9872-136bf0aef8ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR
import Theorems.Thm_GlobalTheory_free_of_finite_of_isTorsionFree_of_valuationRing

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
theorem _root_.solution [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R (M ⧸ N) :=
  haveI := h.isTorsionFree_quotient
  free_of_finite_of_isTorsionFree_of_valuationRing R (M ⧸ N)
end IsSaturatedSubmodule
end GlobalTheory
