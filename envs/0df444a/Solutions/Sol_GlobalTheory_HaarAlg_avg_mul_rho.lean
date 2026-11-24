-- Prove2me | solution 1 for GlobalTheory.HaarAlg.avg_mul_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:40:12.113791+00:00
-- url     : https://prove2.me/submissions/4d174d3e-20ed-4f0f-8f53-4facdf865b3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsAlgebraicIntegral
import Theorems.Thm_GlobalTheory_HaarAlg_mul_avg
import Theorems.Thm_GlobalTheory_HaarAlg_avg_mul
import Theorems.Thm_GlobalTheory_HaarAlg_avg_const
import Theorems.Thm_GlobalTheory_HaarAlg_avg_left
import Theorems.Thm_GlobalTheory_HaarAlg_rho_mul_avg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.HaarAlg
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]
variable [κ.IsMulLeftInvariant]
namespace GlobalTheory.HaarAlg
theorem _root_.solution (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : avg κ ρ * ρ h = avg κ ρ := by
  have hc : Continuous fun g : K => ρ g⁻¹ := hρ.comp continuous_inv
  have h1 : ∀ h, avg κ (fun g => ρ g⁻¹) * ρ h = avg κ fun g => ρ g⁻¹ := fun h => by
    rw [avg_mul κ hc, ← avg_left κ (fun g => ρ g⁻¹) h⁻¹]
    simp only [mul_inv_rev, inv_inv, map_mul]
  have h2 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ ρ := by
    rw [avg_mul κ hc]
    simp only [rho_mul_avg κ ρ hρ, avg_const]
  have h3 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ fun g => ρ g⁻¹ := by
    rw [mul_avg κ hρ]
    simp only [h1, avg_const]
  rw [h2.symm.trans h3, h1]
end GlobalTheory.HaarAlg
