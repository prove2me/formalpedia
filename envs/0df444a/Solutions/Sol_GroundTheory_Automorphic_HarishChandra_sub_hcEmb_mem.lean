-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.sub_hcEmb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:38.946715+00:00
-- url     : https://prove2.me/submissions/139a1354-c394-4501-8966-3d862f0cd519

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mem_nMinusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mem_nPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_isDiagExp_or
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_isDiagExp_of_hasLower
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_isDiagExp_of_hasUpper
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_span_canon_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (u : U n) : u - hcEmb (hcProjLin u) ∈ nMinusU n ⊔ nPlusU n := by
  let φ : U n →ₗ[ℂ] U n := LinearMap.id - hcEmb.toLinearMap ∘ₗ hcProjLin
  have hφ : ∀ u, φ u = u - hcEmb (hcProjLin u) := fun _ => rfl
  suffices ⊤ ≤ (nMinusU n ⊔ nPlusU n).comap φ by
    have := this (Submodule.mem_top (x := u))
    rwa [Submodule.mem_comap, hφ] at this
  rw [← span_canon_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, hφ]
  rcases isDiagExp_or m with h | h | h
  · rw [hcProjLin_canon_of_isDiagExp h, ← canon_of_isDiagExp h, sub_self]
    exact Submodule.zero_mem _
  · rw [hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper h), map_zero, sub_zero]
    exact Submodule.mem_sup_right (canon_mem_nPlusU h)
  · rw [hcProjLin_canon_of_not (not_isDiagExp_of_hasLower h), map_zero, sub_zero]
    exact Submodule.mem_sup_left (canon_mem_nMinusU h)
end GroundTheory.Automorphic.HarishChandra
