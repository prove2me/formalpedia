-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.IsSmoothContinuous.continuous_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:11.989579+00:00
-- url     : https://prove2.me/submissions/e521b306-0640-4cd1-8cf1-3fab82a048cf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_Frechet
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_smoothMap
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_wordOp_map
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_sub
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
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


attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_smoothMap

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
variable {h π}
namespace GroundTheory.Automorphic.IsExpLieAlgebra
namespace IsSmoothContinuous
theorem _root_.solution (hπ : ∀ g, ‖π g‖ ≤ 1)
    {l : h.smoothVectors π →ₗ[ℂ] ℂ} (hl : h.IsSmoothContinuous π l) {v : E}
    (hv : h.IsSmoothVector π v) : Continuous fun g : G => l (h.smoothMap π hv g) := by
  obtain ⟨s, C, hC⟩ := hl
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hY : ∀ Y ∈ s, Tendsto (fun g : G => ‖h.wordOp π Y.2 (π g v) - h.wordOp π Y.2 (π g₀ v)‖)
      (𝓝 g₀) (𝓝 0) := fun Y _ => tendsto_iff_norm_sub_tendsto_zero.1
        ((h.continuous_wordOp_map π hπ hv Y.2).tendsto g₀)
  have hS := tendsto_finsetSum s hY
  simp only [Finset.sum_const_zero] at hS
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => ?_) (by simpa using hS.const_mul |C|)
  rw [← map_sub]
  refine (hC _).trans ?_
  have e : ∀ Y : (Σ k, Fin k → 𝔤),
      h.wordOp π Y.2 ((h.smoothMap π hv g - h.smoothMap π hv g₀ : h.smoothVectors π) : E) =
        h.wordOp π Y.2 (π g v) - h.wordOp π Y.2 (π g₀ v) := fun Y => by
    simp only [Submodule.coe_sub, coe_smoothMap]
    exact h.wordOp_sub π (h.isSmoothVector_map π hv g) (h.isSmoothVector_map π hv g₀) Y.2
  simp_rw [e]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
end IsSmoothContinuous
end GroundTheory.Automorphic.IsExpLieAlgebra
