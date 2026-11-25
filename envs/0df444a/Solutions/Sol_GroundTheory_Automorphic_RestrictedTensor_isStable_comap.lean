-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isStable_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:31.370613+00:00
-- url     : https://prove2.me/submissions/b29c0623-849e-4b94-9eca-b2821f839980

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_fixedProj_mem
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_apply

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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (X : Subrepresentation ρ) :
    IsStable (heckeOps hρ hKc hKo) (X.toSubmodule.comap (fixedVectors ρ K).subtype) := by
  rintro _ ⟨g, rfl⟩ m hm
  rw [Submodule.mem_comap, heckeOp_apply]
  exact fixedProj_mem hρ hKc hKo X (X.apply_mem_toSubmodule g hm)
end GroundTheory.Automorphic.RestrictedTensor
