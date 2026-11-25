-- Prove2me | solution 1 for GlobalTheory.IsSaturatedIn.exists_disjoint_sup_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:00:14.821272+00:00
-- url     : https://prove2.me/submissions/fb8b5cc5-a5ea-4e98-926c-aebdb6fde487

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR
import Theorems.Thm_GlobalTheory_exists_disjoint_sup_eq_of_isCompl_submoduleOf
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
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
namespace IsSaturatedIn
theorem _root_.solution {P N : Submodule R M} [Module.Finite R P]
    (h : IsSaturatedIn P N) : ∃ N' : Submodule R M, Disjoint N N' ∧ N ⊔ N' = P := by
  obtain ⟨Q, hQ⟩ := (isSaturatedIn_iff.1 h).2.exists_isCompl
  exact exists_disjoint_sup_eq_of_isCompl_submoduleOf h.le hQ
end IsSaturatedIn
end GlobalTheory
