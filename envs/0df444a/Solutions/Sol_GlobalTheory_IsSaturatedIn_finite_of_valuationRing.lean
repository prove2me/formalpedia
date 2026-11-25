-- Prove2me | solution 1 for GlobalTheory.IsSaturatedIn.finite_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:46.675276+00:00
-- url     : https://prove2.me/submissions/96c38ab1-4ebd-4633-b764-9b407bdc7fba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR
import Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_finite_of_valuationRing
import Theorems.Thm_GlobalTheory_isSaturatedIn_iff


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
namespace IsSaturatedIn
theorem _root_.solution {P N : Submodule R M} [Module.Finite R P]
    (h : IsSaturatedIn P N) : Module.Finite R N :=
  haveI := (isSaturatedIn_iff.1 h).2.finite_of_valuationRing
  Module.Finite.equiv (Submodule.submoduleOfEquivOfLe h.le)
end IsSaturatedIn
end GlobalTheory
