-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.isoProj_mem_isotypicComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:26:30.405469+00:00
-- url     : https://prove2.me/submissions/60e1623e-b120-40ad-b25a-228a19fb4563

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite

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
theorem _root_.solution {c : Submodule R M} (hc : c ∈ isotypicComponents R M)
    (x : M) : isoProj hc x ∈ c :=
  Subtype.prop _
end GroundTheory.Automorphic.CompactRep
