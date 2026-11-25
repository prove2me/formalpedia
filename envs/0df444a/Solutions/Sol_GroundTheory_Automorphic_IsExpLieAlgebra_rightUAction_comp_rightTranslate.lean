-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.rightUAction_comp_rightTranslate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:45.659401+00:00
-- url     : https://prove2.me/submissions/b9fe77d8-a718-4ba4-9814-c605bee17a6c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_conjTranslate_comp_rightUAction
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
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
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (a : G) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    h.rightUAction (F := F) u * h.rightTranslateEnd a =
      h.rightTranslateEnd a * h.rightUAction (h.AdU a⁻¹ u) := by
  have := congrArg (fun φ => φ u) (h.conjTranslate_comp_rightUAction (F := F) a)
  simp only [AlgHom.comp_apply, conjTranslate, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk] at this
  rw [← this, ← mul_assoc, ← mul_assoc, rightTranslateEnd_mul_inv, one_mul]
end GroundTheory.Automorphic.IsExpLieAlgebra
