-- Prove2me | solution 1 for GlobalTheory.PlaceModel.modul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:42.11181+00:00
-- url     : https://prove2.me/submissions/96a1bb55-4eb0-4928-a526-d30010818d0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Theorems.Thm_GlobalTheory_PlaceModel_wave_modul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
theorem _root_.solution (h : IsBichar χ) {Φ : G → ℂ} (hΦ : Φ ∈ waveSpan χ X Y L) {y : G} (hy : y ∈ Y) :
    (fun t => χ t y * Φ t) ∈ waveSpan χ X Y L := by
  have hle : waveSpan χ X Y L ≤
      (waveSpan χ X Y L).comap (LinearMap.mulLeft ℂ (fun t : G => χ t y)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x₀, hx₀, y₀, hy₀, rfl⟩
    show (fun t => χ t y * wave χ L x₀ y₀ t) ∈ waveSpan χ X Y L
    rw [wave_modul h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x₀, hx₀, y + y₀, Y.add_mem hy hy₀, rfl⟩)
  exact hle hΦ
end GlobalTheory.PlaceModel
