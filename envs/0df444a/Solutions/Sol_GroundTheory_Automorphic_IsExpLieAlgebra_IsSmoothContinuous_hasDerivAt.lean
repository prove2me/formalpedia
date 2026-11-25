-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.IsSmoothContinuous.hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:21:44.630325+00:00
-- url     : https://prove2.me/submissions/3e1c8eff-15d0-435e-878f-898a99a428ec

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_Frechet
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_smul
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
theorem _root_.solution {l : h.smoothVectors π →ₗ[ℂ] ℂ}
    (hl : h.IsSmoothContinuous π l) {u : ℝ → h.smoothVectors π} {d : h.smoothVectors π}
    (hu : ∀ Y : (Σ k, Fin k → 𝔤),
      HasDerivAt (fun t => h.wordOp π Y.2 (u t : E)) (h.wordOp π Y.2 (d : E)) 0) :
    HasDerivAt (fun t => l (u t)) (l d) 0 := by
  obtain ⟨s, C, hC⟩ := hl
  rw [hasDerivAt_iff_isLittleO]
  have hY : ∀ Y ∈ s, (fun t : ℝ => ‖h.wordOp π Y.2 (u t : E) - h.wordOp π Y.2 (u 0 : E) -
      (t - 0) • h.wordOp π Y.2 (d : E)‖) =o[𝓝 0] fun t => t - 0 :=
    fun Y _ => (hasDerivAt_iff_isLittleO.1 (hu Y)).norm_left
  have hS := IsLittleO.sum hY
  refine IsBigO.trans_isLittleO (IsBigO.of_bound |C| (Eventually.of_forall fun t => ?_)) hS
  have e : l (u t) - l (u 0) - (t - 0) • l d = l (u t - u 0 - ((t : ℂ) • d)) := by
    rw [map_sub, map_sub, map_smul, smul_eq_mul, Complex.real_smul, sub_zero]
  have e2 : ∀ Y : (Σ k, Fin k → 𝔤), h.wordOp π Y.2 ((u t - u 0 - ((t : ℂ) • d) : h.smoothVectors π) : E) =
      h.wordOp π Y.2 (u t : E) - h.wordOp π Y.2 (u 0 : E) - (t - 0) • h.wordOp π Y.2 (d : E) := by
    intro Y
    simp only [Submodule.coe_sub, Submodule.coe_smul]
    rw [h.wordOp_sub π ((h.smoothVectors π).sub_mem (u t).2 (u 0).2)
      ((h.smoothVectors π).smul_mem _ d.2), h.wordOp_sub π (u t).2 (u 0).2,
      h.wordOp_smul π d.2, sub_zero, Complex.coe_smul]
  rw [e]
  refine (hC _).trans ?_
  simp_rw [e2]
  rw [Finset.sum_apply, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
end IsSmoothContinuous
end GroundTheory.Automorphic.IsExpLieAlgebra
