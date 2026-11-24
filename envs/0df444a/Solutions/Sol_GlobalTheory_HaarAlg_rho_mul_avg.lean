-- Prove2me | solution 1 for GlobalTheory.HaarAlg.rho_mul_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:08.332553+00:00
-- url     : https://prove2.me/submissions/6889005d-0c2f-4aa3-a78c-60d5114e05c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsAlgebraicIntegral
import Theorems.Thm_GlobalTheory_HaarAlg_mul_avg
import Theorems.Thm_GlobalTheory_HaarAlg_avg_left

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
theorem _root_.solution (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : ρ h * avg κ ρ = avg κ ρ := by
  rw [mul_avg κ hρ, ← avg_left κ ρ h]
  simp only [map_mul]
end GlobalTheory.HaarAlg
