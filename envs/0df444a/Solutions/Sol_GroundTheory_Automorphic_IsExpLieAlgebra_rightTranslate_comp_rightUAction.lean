-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.rightTranslate_comp_rightUAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:10.601913+00:00
-- url     : https://prove2.me/submissions/9c3479fc-13fa-471d-935e-99f5691d17fc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdU_inv_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction_comp_rightTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    h.rightTranslateEnd (F := F) a * h.rightUAction u =
      h.rightUAction (h.AdU a u) * h.rightTranslateEnd a := by
  rw [rightUAction_comp_rightTranslate, AdU_inv_apply]
end GroundTheory.Automorphic.IsExpLieAlgebra
