-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.continuous_apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:43:57.716667+00:00
-- url     : https://prove2.me/submissions/f21f1479-416c-42fc-a41e-96953a45ab0f

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
theorem _root_.solution (hπ : ∀ g, ‖π g‖ ≤ 1) {T : Type*} [TopologicalSpace T]
    {p : T → G} {u : T → E} (hp : Continuous p) (hu : Continuous u) :
    Continuous fun x => π (p x) (u x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun x => ‖u x - u x₀‖) (𝓝 x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hu.tendsto x₀)
  have h2 : Tendsto (fun x => ‖π (p x) (u x₀) - π (p x₀) (u x₀)‖) (𝓝 x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (((π.continuous_orbit (u x₀)).comp hp).tendsto x₀)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) (by simpa using h1.add h2)
  calc ‖π (p x) (u x) - π (p x₀) (u x₀)‖
      = ‖π (p x) (u x - u x₀) + (π (p x) (u x₀) - π (p x₀) (u x₀))‖ := by
        rw [map_sub]; try abel
    _ ≤ ‖π (p x) (u x - u x₀)‖ + ‖π (p x) (u x₀) - π (p x₀) (u x₀)‖ := norm_add_le _ _
    _ ≤ ‖u x - u x₀‖ + ‖π (p x) (u x₀) - π (p x₀) (u x₀)‖ := by
        gcongr
        calc ‖π (p x) (u x - u x₀)‖ ≤ ‖π (p x)‖ * ‖u x - u x₀‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖u x - u x₀‖ := by gcongr; exact hπ _
          _ = _ := one_mul _
end GroundTheory.Automorphic.IsExpLieAlgebra
