-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isSimpleUnder_heckeOps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:57.276051+00:00
-- url     : https://prove2.me/submissions/82252f91-4a1a-4323-8ff3-11b9bea176cf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_mem_heckeOps
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_span_orbit
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem


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
theorem _root_.solution [ρ.IsIrreducible] (hK : fixedVectors ρ K ≠ ⊥) :
    IsSimpleUnder (heckeOps hρ hKc hKo) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hK, fun p hp => ?_⟩
  by_cases hp0 : p = ⊥
  · exact Or.inl hp0
  right
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hm0' : (m : V) ≠ 0 := fun h => hm0 (Subtype.ext h)
  rw [eq_top_iff]
  intro m' _
  have hle : Submodule.span ℂ (range fun g => ρ g (m : V)) ≤
      p.comap ((fixedProj ρ hρ hKc hKo)) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hp _ (heckeOp_mem_heckeOps hρ hKc hKo g) m hm
  have := hle (mem_span_orbit (ρ := ρ) hm0' (m' : V))
  rw [Submodule.mem_comap] at this
  have he : fixedProj ρ hρ hKc hKo (m' : V) = m' :=
    Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo m'.2)
  rwa [he] at this
end GroundTheory.Automorphic.RestrictedTensor
