-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.rightDerivEnd_mul_leftTranslateEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:49:13.174873+00:00
-- url     : https://prove2.me/submissions/789d1489-7342-421b-8857-10bc1d167482

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_AutomorphicFormSpaces_LeftTranslate
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightDeriv_leftTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (X : 𝔤) (a : G) :
    h.rightDerivEnd (F := F) X * h.leftTranslateEnd a = h.leftTranslateEnd a * h.rightDerivEnd X :=
  LinearMap.ext fun f => Subtype.ext (h.rightDeriv_leftTranslate X (f : G → F) a)
end GroundTheory.Automorphic.IsExpLieAlgebra
