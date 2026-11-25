-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigmaL_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:25:10.406673+00:00
-- url     : https://prove2.me/submissions/79875f71-f7d6-4109-8297-2d49d0730ded

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_swapTheta_swapTheta
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_swapTheta_inv
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigmaL_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [TopologicalSpace F] [IsTopologicalRing F]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (h : NN F n) (f : GL (Fin n) F → ℂ) :
    sigmaL (transl h f) = transl (swapTheta h) (sigmaL f) := by
  funext x
  simp only [sigmaL_apply, transl_apply]
  congr 1
  rw [sigma_smul, swapTheta_inv, swapTheta_swapTheta]
end GroundTheory.Automorphic.Whittaker
