-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.IsSmoothContinuous.exists_norm_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:19.299852+00:00
-- url     : https://prove2.me/submissions/161f709e-c765-473c-8207-e4694338eb5d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_Frechet
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_norm_wordOp_map_le


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
variable {h π}
namespace GroundTheory.Automorphic.IsExpLieAlgebra
namespace IsSmoothContinuous
theorem _root_.solution (hπ : ∀ g, ‖π g‖ ≤ 1)
    {l : h.smoothVectors π →ₗ[ℂ] ℂ} (hl : h.IsSmoothContinuous π l) {v : E}
    (hv : h.IsSmoothVector π v) :
    ∃ C N, ∀ g : G, ‖l (h.smoothMap π hv g)‖ ≤ C * (1 + ‖h.AdL g⁻¹‖) ^ N := by
  obtain ⟨s, C, hC⟩ := hl
  choose D hD using fun Y : (Σ k, Fin k → 𝔤) => h.exists_norm_wordOp_map_le π hπ hv Y.2
  set N := s.sup fun Y => Y.1
  refine ⟨|C| * ∑ Y ∈ s, |D Y|, N, fun g => ?_⟩
  have h1 : 1 ≤ 1 + ‖h.AdL g⁻¹‖ := le_add_of_nonneg_right (by positivity)
  have hterm : ∀ Y ∈ s, ‖h.wordOp π Y.2 (π g v)‖ ≤ |D Y| * (1 + ‖h.AdL g⁻¹‖) ^ N := by
    intro Y hY
    calc ‖h.wordOp π Y.2 (π g v)‖ ≤ D Y * ‖h.AdL g⁻¹‖ ^ Y.1 := hD Y g
      _ ≤ |D Y| * ‖h.AdL g⁻¹‖ ^ Y.1 := by gcongr; exact le_abs_self _
      _ ≤ |D Y| * (1 + ‖h.AdL g⁻¹‖) ^ Y.1 := by
          gcongr; exact le_add_of_nonneg_left zero_le_one
      _ ≤ |D Y| * (1 + ‖h.AdL g⁻¹‖) ^ N := by
          gcongr
          exact Finset.le_sup (f := fun Y : (Σ k, Fin k → 𝔤) => Y.1) hY
  calc ‖l (h.smoothMap π hv g)‖ ≤ C * ∑ Y ∈ s, ‖h.wordOp π Y.2 (π g v)‖ := hC _
    _ ≤ |C| * ∑ Y ∈ s, ‖h.wordOp π Y.2 (π g v)‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ ≤ |C| * ∑ Y ∈ s, |D Y| * (1 + ‖h.AdL g⁻¹‖) ^ N := by
        gcongr with Y hY
        exact hterm Y hY
    _ = |C| * (∑ Y ∈ s, |D Y|) * (1 + ‖h.AdL g⁻¹‖) ^ N := by
        rw [← Finset.sum_mul]; ring
end IsSmoothContinuous
end GroundTheory.Automorphic.IsExpLieAlgebra
