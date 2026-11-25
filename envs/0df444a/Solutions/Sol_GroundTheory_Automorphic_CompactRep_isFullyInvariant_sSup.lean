-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.isFullyInvariant_sSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:25.701401+00:00
-- url     : https://prove2.me/submissions/3a25a6a3-cc8d-4a07-a1f1-a1be0a933091

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans


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
theorem _root_.solution {s : Set (Submodule R M)} (h : ∀ m ∈ s, m.IsFullyInvariant) :
    (sSup s).IsFullyInvariant := fun f =>
  sSup_le fun m hm => (h m hm f).trans (Submodule.comap_mono (le_sSup hm))
end GroundTheory.Automorphic.CompactRep
