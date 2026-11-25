-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.rightDeriv_rightTranslate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:23.233102+00:00
-- url     : https://prove2.me/submissions/6ab0f39c-612c-4b7b-abce-06efcf32d6e1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_Ad
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



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {f : G → F} (hf : h.IsSmoothFun f) (a : G) (X : 𝔤) :
    h.rightDeriv X (rightTranslate a f) = rightTranslate a (h.rightDeriv (h.Ad a⁻¹ X) f) := by
  funext g
  simp only [rightDeriv, rightTranslate]
  have e : (fun Y : 𝔤 => f (g * h.expG Y * a)) =
      (fun Y : 𝔤 => f (g * a * h.expG Y)) ∘ h.AdL a⁻¹ := by
    funext Y
    simp only [Function.comp_apply, AdL_apply, expG_Ad, inv_inv]
    congr 1
    group
  rw [e]
  have hF : HasFDerivAt (fun Y : 𝔤 => f (g * a * h.expG Y))
      (fderiv ℝ (fun Y : 𝔤 => f (g * a * h.expG Y)) 0) (h.AdL a⁻¹ 0) := by
    simpa using (h.differentiable_comp_expG hf (g * a) 0).hasFDerivAt
  rw [(hF.comp (0 : 𝔤) (h.AdL a⁻¹).hasFDerivAt).fderiv]
  rfl
end GroundTheory.Automorphic.IsExpLieAlgebra
