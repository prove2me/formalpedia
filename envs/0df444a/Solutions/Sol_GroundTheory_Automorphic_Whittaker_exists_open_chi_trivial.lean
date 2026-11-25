-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_open_chi_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:11.798777+00:00
-- url     : https://prove2.me/submissions/1fcb6034-060b-4fbe-9c70-37990f11402f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_chi_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_compactOpen_psiN_trivial


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
theorem _root_.solution (hψ : Continuous ψ₀) :
    ∃ L : Subgroup (NN F n), IsOpen (L : Set (NN F n)) ∧ ∀ l ∈ L, chi ψ₀ l = 1 := by
  obtain ⟨K, -, hKo, hKψ⟩ := exists_compactOpen_psiN_trivial F n hψ
  refine ⟨K.prod K, ?_, fun l hl => ?_⟩
  · rw [Subgroup.coe_prod]
    exact hKo.prod hKo
  · rw [chi_apply, hKψ _ hl.1, hKψ _ hl.2, inv_one, mul_one]
end GroundTheory.Automorphic.Whittaker
