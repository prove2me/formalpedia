-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.fixedProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:37.858815+00:00
-- url     : https://prove2.me/submissions/96348f88-dd2a-4035-b3bd-945e74dc5921

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_sub_fixedProj_mem_span

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
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (X : Subrepresentation ρ) {x : V} (hx : x ∈ X.toSubmodule) :
    (fixedProj ρ hρ hKc hKo x : V) ∈ X.toSubmodule := by
  have h1 := sub_fixedProj_mem_span hρ hKc hKo x
  have h2 : Submodule.span ℂ (range fun k : K => ρ k x - x) ≤ X.toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact X.toSubmodule.sub_mem (X.apply_mem_toSubmodule _ hx) hx
  have := X.toSubmodule.sub_mem hx (h2 h1)
  rwa [sub_sub_cancel] at this
end GroundTheory.Automorphic.RestrictedTensor
