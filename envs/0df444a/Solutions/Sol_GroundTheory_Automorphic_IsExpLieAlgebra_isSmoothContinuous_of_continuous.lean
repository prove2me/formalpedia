-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothContinuous_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:40.535222+00:00
-- url     : https://prove2.me/submissions/daf8e7a0-c9e5-46bd-8371-4e3bbc75fea3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_Frechet
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_IsTestFunction_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (l : h.SmoothFrechet π →L[ℂ] ℂ) :
    h.IsSmoothContinuous π (l.toLinearMap : h.smoothVectors π →ₗ[ℂ] ℂ) := by
  set q : Seminorm ℂ (h.SmoothFrechet π) := (normSeminorm ℂ ℂ).comp l.toLinearMap with hq
  have hqc : Continuous q := continuous_norm.comp l.continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (h.withSeminorms_smoothFrechet π) q hqc
  refine ⟨s, C, fun v => ?_⟩
  have h1 : q v ≤ (C • s.sup (h.smoothSeminormFamily π)) v := hC v
  have h2 : (s.sup (h.smoothSeminormFamily π)) v ≤ ∑ Y ∈ s, ‖h.wordOp π Y.2 (v : E)‖ := by
    refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun Y hY => ?_
    exact Finset.single_le_sum (f := fun Y : (Σ k, Fin k → 𝔤) => ‖h.wordOp π Y.2 (v : E)‖)
      (fun _ _ => norm_nonneg _) hY
  calc ‖(l.toLinearMap : h.smoothVectors π →ₗ[ℂ] ℂ) v‖ = q v := rfl
    _ ≤ (C • s.sup (h.smoothSeminormFamily π)) v := h1
    _ = C * (s.sup (h.smoothSeminormFamily π)) v := rfl
    _ ≤ C * ∑ Y ∈ s, ‖h.wordOp π Y.2 (v : E)‖ := by gcongr
end GroundTheory.Automorphic.IsExpLieAlgebra
