-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_expG_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:21.113799+00:00
-- url     : https://prove2.me/submissions/37e078e7-29a6-48b4-aeeb-07980f4be2cd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_BanachRep_continuous_orbit
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
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
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (hπ : ∀ g, ‖π g‖ ≤ 1) {w : ℝ → E} {w' : E}
    (hw : HasDerivAt w w' 0) (hw0 : h.IsSmoothVector π (w 0)) (X : 𝔤) :
    HasDerivAt (fun t : ℝ => π (h.expG (t • X)) (w t)) (h.derivOp π X (w 0) + w') 0 := by
  have hA := h.hasDerivAt_derivOp π hw0 X
  have hB : HasDerivAt (fun t : ℝ => π (h.expG (t • X)) (w t - w 0)) w' 0 := by
    rw [hasDerivAt_iff_isLittleO] at hw ⊢
    have hc : Tendsto (fun t : ℝ => π (h.expG (t • X)) w') (𝓝 0) (𝓝 w') := by
      have hcont : Continuous fun t : ℝ => π (h.expG (t • X)) w' :=
        (π.continuous_orbit w').comp (h.continuous_expG.comp (continuous_id.smul continuous_const))
      simpa using hcont.tendsto 0
    rw [isLittleO_iff] at hw ⊢
    intro c hc0
    have h1 := hw (half_pos hc0)
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), ‖π (h.expG (t • X)) w' - w'‖ ≤ c / 2 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hc)
      exact (this.eventually (ge_mem_nhds (half_pos hc0))).mono fun t ht => ht
    filter_upwards [h1, h2] with t ht1 ht2
    simp only [sub_zero, zero_smul, sub_self, map_zero] at ht1 ⊢
    have e : π (h.expG (t • X)) (w t - w 0) - t • w' =
        π (h.expG (t • X)) (w t - w 0 - t • w') + t • (π (h.expG (t • X)) w' - w') := by
      simp only [map_sub, ContinuousLinearMap.map_smul_of_tower, smul_sub]; abel
    rw [e]
    calc ‖π (h.expG (t • X)) (w t - w 0 - t • w') + t • (π (h.expG (t • X)) w' - w')‖
        ≤ ‖π (h.expG (t • X)) (w t - w 0 - t • w')‖ + ‖t • (π (h.expG (t • X)) w' - w')‖ :=
          norm_add_le _ _
      _ ≤ ‖w t - w 0 - t • w'‖ + ‖t‖ * (c / 2) := by
          gcongr
          · calc ‖π (h.expG (t • X)) (w t - w 0 - t • w')‖
                ≤ ‖π (h.expG (t • X))‖ * ‖w t - w 0 - t • w'‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * ‖w t - w 0 - t • w'‖ := by gcongr; exact hπ _
              _ = _ := one_mul _
          · rw [norm_smul]; gcongr
      _ ≤ c / 2 * ‖t‖ + ‖t‖ * (c / 2) := by gcongr
      _ = c * ‖t‖ := by ring
  have := hA.add hB
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, map_sub]
  abel
end GroundTheory.Automorphic.IsExpLieAlgebra
