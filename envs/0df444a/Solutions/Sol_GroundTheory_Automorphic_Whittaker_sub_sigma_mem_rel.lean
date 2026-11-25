-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sub_sigma_mem_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:51.960197+00:00
-- url     : https://prove2.me/submissions/0caefaec-85ab-4440-b281-9716baa7ddfc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_good_nhds
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) {f : GL (Fin n) F → ℂ}
    (hf : f ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    f - sigmaL f ∈ rel n ψ₀ := by
  have key : supportedIn (univ : Set (GL (Fin n) F)) ≤ goodSub n ψ₀ :=
    supportedIn_le_of_local fun x _ => exists_good_nhds ψ₀ hψ hψ₁ x
  exact key ⟨hf, subset_univ _⟩
end GroundTheory.Automorphic.Whittaker
