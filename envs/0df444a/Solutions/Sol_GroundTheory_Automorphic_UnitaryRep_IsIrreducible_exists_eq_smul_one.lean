-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsIrreducible.exists_eq_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:23:23.281007+00:00
-- url     : https://prove2.me/submissions/e4e47cf1-a112-41b7-bc43-3f47a48a09b5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsIrreducible_exists_eq_algebraMap_of_isSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_star_mem_intertwiners


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hπ : π.IsIrreducible) {T : H →L[ℂ] H}
    (hT : T ∈ π.intertwiners π) : ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  have hstar := star_mem_intertwiners hT
  have hre : (ℜ T : H →L[ℂ] H) ∈ π.intertwiners π := by
    rw [realPart_apply_coe]
    exact Submodule.smul_of_tower_mem _ _ (add_mem hT hstar)
  have him : (ℑ T : H →L[ℂ] H) ∈ π.intertwiners π := by
    rw [imaginaryPart_apply_coe]
    exact Submodule.smul_mem _ _ (Submodule.smul_of_tower_mem _ _ (sub_mem hT hstar))
  obtain ⟨a, ha⟩ := hπ.exists_eq_algebraMap_of_isSelfAdjoint hre (ℜ T).2
  obtain ⟨b, hb⟩ := hπ.exists_eq_algebraMap_of_isSelfAdjoint him (ℑ T).2
  refine ⟨a + I * b, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T, ha, hb]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← add_smul]
end IsIrreducible
end GroundTheory.Automorphic.UnitaryRep
