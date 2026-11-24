-- Prove2me | solution 1 for GlobalTheory.IsSaturatedSubmodule.exists_isCompl_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:39.193843+00:00
-- url     : https://prove2.me/submissions/6e219ed3-8ebe-4e35-92be-160987a170ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR
import Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_free_quotient_of_valuationRing

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
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : ∃ N' : Submodule R M, IsCompl N N' :=
  haveI := h.free_quotient_of_valuationRing
  exists_isCompl_of_projective_quotient N
end IsSaturatedSubmodule
end GlobalTheory
