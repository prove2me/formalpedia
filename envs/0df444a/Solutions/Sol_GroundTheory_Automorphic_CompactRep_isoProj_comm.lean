-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.isoProj_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:35.340286+00:00
-- url     : https://prove2.me/submissions/9d90fee7-dd17-4690-b8fa-0c716ba0d32f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isFullyInvariant_sSup
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isoProj_apply_of_mem
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isoProj_apply_of_mem_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.CompactRep
open Module Set
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X]
variable {σ : Representation ℂ K X}
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
namespace GroundTheory.Automorphic.CompactRep
theorem _root_.solution {c : Submodule R M} (hc : c ∈ isotypicComponents R M) (f : Module.End R M)
    (x : M) : isoProj hc (f x) = f (isoProj hc x) := by
  have hcompl := isCompl_isotypicComponent hc
  have hfc : c.IsFullyInvariant := Submodule.IsFullyInvariant.of_mem_isotypicComponents hc
  have hfr : (sSup (isotypicComponents R M \ {c})).IsFullyInvariant :=
    isFullyInvariant_sSup fun m hm => Submodule.IsFullyInvariant.of_mem_isotypicComponents hm.1
  have hx : x ∈ c ⊔ sSup (isotypicComponents R M \ {c}) := by
    rw [codisjoint_iff.1 hcompl.2]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add f, map_add (isoProj hc), map_add (isoProj hc), isoProj_apply_of_mem hc (hfc f ha),
    isoProj_apply_of_mem_compl hc (hfr f hb), isoProj_apply_of_mem hc ha,
    isoProj_apply_of_mem_compl hc hb, add_zero, add_zero]
end GroundTheory.Automorphic.CompactRep
