-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:44:03.043151+00:00
-- url     : https://prove2.me/submissions/a2b1d11b-593b-4c7e-a1cf-533188efcd85

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
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


attribute [local simp] GroundTheory.Automorphic.conjCME_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace GroundTheory.Automorphic
namespace IsExpLieAlgebra
theorem _root_.solution (h : IsExpLieAlgebra G 𝔤) : IsClosed (G : Set 𝔸ˣ) := by
  set W : Set 𝔸ˣ := (fun u : 𝔸ˣ => (u : 𝔸)) ⁻¹' h.nhdOne with hW
  have hWo : IsOpen W := h.isOpen_nhdOne.preimage Units.continuous_val
  refine isClosed_of_closure_subset fun x hx => ?_
  have hN : {z : 𝔸ˣ | z⁻¹ * x ∈ W} ∈ 𝓝 x := by
    refine (hWo.preimage (continuous_inv.mul continuous_const)).mem_nhds ?_
    show (((x⁻¹ * x : 𝔸ˣ)) : 𝔸) ∈ h.nhdOne
    simpa using h.one_mem_nhdOne
  obtain ⟨g₀, hg₀N, hg₀G⟩ := mem_closure_iff_nhds.1 hx _ hN
  set y := g₀⁻¹ * x with hy
  have hyW : y ∈ W := hg₀N
  have hyc : y ∈ closure (G : Set 𝔸ˣ) :=
    map_mem_closure (continuous_const.mul continuous_id) hx fun z hz =>
      G.mul_mem (G.inv_mem hg₀G) hz
  have hyc' : y ∈ closure (W ∩ (G : Set 𝔸ˣ)) := hWo.inter_closure ⟨hyW, hyc⟩
  set L : 𝔸ˣ → 𝔸 := fun u => (expPartialHomeomorph ℝ 𝔸).symm (u : 𝔸) with hLdef
  have hL : ContinuousAt L y :=
    ((expPartialHomeomorph ℝ 𝔸).continuousAt_symm (h.nhdOne_subset_target hyW)).comp
      Units.continuous_val.continuousAt
  have himg : L '' (W ∩ (G : Set 𝔸ˣ)) ⊆ (𝔤 : Set 𝔸) := by
    rintro _ ⟨u, ⟨huW, huG⟩, rfl⟩
    apply h.mem_of_mem_nhd (h.symm_mem_nhd huW)
    have : expUnit ℝ 𝔸 (L u) = u := Units.ext (h.exp_symm huW)
    rw [this]
    exact huG
  have hLy : L y ∈ 𝔤 :=
    (Submodule.closed_of_finiteDimensional 𝔤).closure_subset_iff.2 himg (mem_closure_image hL hyc')
  have hyG : y ∈ G := by
    have : expUnit ℝ 𝔸 (L y) = y := Units.ext (h.exp_symm hyW)
    rw [← this]
    exact h.expUnit_mem _ hLy
  have : x = g₀ * y := by rw [hy, mul_inv_cancel_left]
  rw [this]
  exact G.mul_mem hg₀G hyG
end IsExpLieAlgebra
end GroundTheory.Automorphic
