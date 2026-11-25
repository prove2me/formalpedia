-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.swapTheta_mem_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:52.729583+00:00
-- url     : https://prove2.me/submissions/28b4f961-02a3-43a8-9195-055721a7f9ef

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_thetaN_symm
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
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {K : Subgroup (Iwasawa.unipotent F n)} {l : NN F n}
    (hl : l ∈ (K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom).prod K) :
    swapTheta l ∈ (K.map (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).toMonoidHom).prod K := by
  obtain ⟨⟨k, hk, hk1⟩, hl2⟩ := hl
  refine ⟨⟨l.2, hl2, rfl⟩, ?_⟩
  show thetaN l.1 ∈ K
  rw [← hk1]
  have : thetaN (thetaN k) = k := by
    rw [← thetaN_symm]
    exact MulEquiv.symm_apply_apply _ k
  simpa [this] using hk
end GroundTheory.Automorphic.Whittaker
