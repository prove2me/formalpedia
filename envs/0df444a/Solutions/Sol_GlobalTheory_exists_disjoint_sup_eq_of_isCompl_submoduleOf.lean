-- Prove2me | solution 1 for GlobalTheory.exists_disjoint_sup_eq_of_isCompl_submoduleOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:04.209028+00:00
-- url     : https://prove2.me/submissions/defd4277-e841-49b2-be84-3bd36430bf7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR

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
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution {P N : Submodule R M} (hle : N ≤ P)
    {Q : Submodule R P} (h : IsCompl (N.submoduleOf P) Q) :
    ∃ N' : Submodule R M, Disjoint N N' ∧ N ⊔ N' = P := by
  have hN : (N.submoduleOf P).map P.subtype = N := by
    rw [Submodule.submoduleOf, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  refine ⟨Q.map P.subtype, ?_, ?_⟩
  · rw [← hN, disjoint_iff, ← Submodule.map_inf _ P.injective_subtype, h.inf_eq_bot,
      Submodule.map_bot]
  · conv_lhs => rw [← hN]
    rw [← Submodule.map_sup, h.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
end GlobalTheory
