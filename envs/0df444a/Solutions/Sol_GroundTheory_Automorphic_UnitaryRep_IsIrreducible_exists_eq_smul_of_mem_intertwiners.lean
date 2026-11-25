-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsIrreducible.exists_eq_smul_of_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:27.033536+00:00
-- url     : https://prove2.me/submissions/6d0df263-8996-418f-83d9-3c7cec2508d0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsIrreducible_exists_eq_smul_one
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_adjoint_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_mem_intertwiners
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open scoped InnerProductSpace ComplexConjugate
open scoped ComplexStarModule
open ContinuousLinearMap Complex
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {σ : UnitaryRep G K}
namespace GroundTheory.Automorphic.UnitaryRep
namespace IsIrreducible
theorem _root_.solution (hπ : π.IsIrreducible)
    (hσ : σ.IsIrreducible) {S T : H →L[ℂ] K} (hS : S ∈ π.intertwiners σ)
    (hT : T ∈ π.intertwiners σ) (hS0 : S ≠ 0) : ∃ c : ℂ, T = c • S := by
  obtain ⟨a, ha⟩ := hπ.exists_eq_smul_one
    (comp_mem_intertwiners (adjoint_mem_intertwiners hS) hT)
  obtain ⟨d, hd⟩ := hσ.exists_eq_smul_one
    (comp_mem_intertwiners hS (adjoint_mem_intertwiners hS))
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hS0
    have hSS : S ∘L adjoint S = 0 := by rw [hd, zero_smul]
    have hadj : adjoint S = 0 := by
      ext w
      have h1 : ⟪adjoint S w, adjoint S w⟫_ℂ = ⟪w, (S ∘L adjoint S) w⟫_ℂ := by
        rw [comp_apply, adjoint_inner_left]
      rw [hSS, zero_apply, inner_zero_right, inner_self_eq_zero] at h1
      simpa using h1
    rw [← adjoint_adjoint S, hadj, map_zero]
  refine ⟨a / d, ?_⟩
  have e1 : S ∘L (adjoint S ∘L T) = a • S := by rw [ha]; ext v; simp
  have e2 : (S ∘L adjoint S) ∘L T = d • T := by rw [hd]; ext v; simp
  have e3 : d • T = a • S := by rw [← e1, ← e2, comp_assoc]
  rw [div_eq_inv_mul, mul_smul, ← e3, smul_smul, inv_mul_cancel₀ hd0, one_smul]
end IsIrreducible
end GroundTheory.Automorphic.UnitaryRep
