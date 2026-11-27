-- Prove2me | solution 1 for GlobalTheory.finrank_range_fderiv_lt_of_volume_image_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:26.555177+00:00
-- url     : https://prove2.me/submissions/503acae7-c3e1-4273-81db-8d56e1df1b11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankRangeFderivLtOfVolumeImageEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (h : (Fin n → ℂ) → (Fin n → ℂ)) (W : Set (Fin n → ℂ)), IsOpen W → AnalyticOnNhd ℂ h W → volume (h '' W) = 0 → ∀ y ∈ W, Module.finrank ℂ (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) < n := by
  intro n h W hW ha h0 y hy
  by_contra hlt
  have hn : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  have hle := Submodule.finrank_le
    (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
  have htop : LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  have hs : HasStrictFDerivAt h (fderiv ℂ h y) y := (ha y hy).hasStrictFDerivAt
  have hmap := hs.map_nhds_eq_of_surj htop
  have hmem : h '' W ∈ 𝓝 (h y) := by
    rw [← hmap]
    exact image_mem_map (hW.mem_nhds hy)
  exact (Measure.measure_pos_of_mem_nhds volume hmem).ne' h0
end GlobalTheory
