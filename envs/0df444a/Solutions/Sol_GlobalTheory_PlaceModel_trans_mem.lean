-- Prove2me | solution 1 for GlobalTheory.PlaceModel.trans_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:42.472826+00:00
-- url     : https://prove2.me/submissions/364fd13e-5dcf-4103-9a13-f9df5b781fd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Theorems.Thm_GlobalTheory_PlaceModel_wave_trans

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
theorem _root_.solution {Φ : G → ℂ} (hΦ : Φ ∈ waveSpan χ X Y L) {x : G} (hx : x ∈ X) :
    (fun t => Φ (t + x)) ∈ waveSpan χ X Y L := by
  have hle : waveSpan χ X Y L ≤ (waveSpan χ X Y L).comap (LinearMap.funLeft ℂ ℂ (fun t : G => t + x)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x₀, hx₀, y, hy, rfl⟩
    show (fun t => wave χ L x₀ y (t + x)) ∈ waveSpan χ X Y L
    rw [wave_trans]
    exact Submodule.subset_span ⟨x + x₀, X.add_mem hx hx₀, y, hy, rfl⟩
  exact hle hΦ
end GlobalTheory.PlaceModel
