-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.isAdmissible_gkModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:14.505827+00:00
-- url     : https://prove2.me/submissions/f8b2bd54-2951-4f48-bd4a-048efa60948d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.gkModule_σ_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.gkModule_ρ_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (K : Subgroup G)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution [CompleteSpace E] (hπ : π.IsAdmissible K) :
    (h.gkModule π K).IsAdmissible := by
  intro W _ _ _ τ hirr hcont
  haveI := hπ W τ hirr hcont
  let f : kHom τ (h.gkModule π K).σ →ₗ[ℂ] kHom τ (π.restrict K).toRepresentation :=
    { toFun := fun T => ⟨(h.gkVectors π K).subtype ∘ₗ T.1, fun k => by
        ext w
        have := congrArg Subtype.val (LinearMap.congr_fun (T.2 k) w)
        simpa using this⟩
      map_add' := fun S T => by ext; simp
      map_smul' := fun c T => by ext; simp }
  refine Module.Finite.of_injective f fun S T hST => ?_
  ext w
  have := LinearMap.congr_fun (congrArg Subtype.val hST) w
  simpa [f] using this
end GroundTheory.Automorphic.IsExpLieAlgebra
