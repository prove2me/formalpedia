-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.rightDeriv_mem_of_isKStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:10:45.150429+00:00
-- url     : https://prove2.me/submissions/53735cdd-e710-4386-b6eb-880bf9029cdc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
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
variable (K : Subgroup G)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {V : Submodule ℂ (h.smoothFuns (F := F))}
    [FiniteDimensional ℂ V] (hV : ∀ (k : K), ∀ w ∈ V, h.rightTranslateEnd (k : G) w ∈ V)
    {X : 𝔤} (hX : ∀ t : ℝ, h.expG (t • X) ∈ K) {w : h.smoothFuns (F := F)} (hw : w ∈ V) :
    h.rightDerivEnd X w ∈ V := by
  set V' : Submodule ℂ (G → F) := V.map (h.smoothFuns (F := F)).subtype
  haveI : FiniteDimensional ℂ V' := inferInstance
  have hcl : IsClosed (V' : Set (G → F)) := Submodule.closed_of_finiteDimensional V'
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (rightTranslate (h.expG (t • X)) (w : G → F) - w))
      (𝓝[≠] 0) (𝓝 (h.rightDeriv X w)) := by
    rw [tendsto_pi_nhds]
    intro g
    have := hasDerivAt_iff_tendsto_slope.1 (h.hasDerivAt_rightDeriv w.2 X g)
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp [slope_def_module, rightTranslate]
  have hmem : h.rightDeriv X w ∈ V' := by
    refine hcl.mem_of_tendsto hlim (Eventually.of_forall fun t => ?_)
    have h1 := hV ⟨h.expG (t • X), hX t⟩ w hw
    refine Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact ⟨_, h1, rfl⟩
    · exact ⟨w, hw, rfl⟩
  obtain ⟨w', hw', he⟩ := hmem
  have : w' = h.rightDerivEnd X w := Subtype.ext he
  rwa [← this]
end GroundTheory.Automorphic.IsExpLieAlgebra
