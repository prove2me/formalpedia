-- Prove2me | solution 1 for GlobalTheory.DoubleCosetAdjoint.setIntegral_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:25:03.119239+00:00
-- url     : https://prove2.me/submissions/dd4bc804-ca1d-4c32-bd6e-56c13c295287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomain
import Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_isFundamentalDomain_mul_right
import Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_preimage_preimage_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.DoubleCosetAdjoint
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)
namespace GlobalTheory.DoubleCosetAdjoint
theorem _root_.solution (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  have h1 := (measurePreserving_mul_right μ y).setIntegral_preimage_emb
    (measurableEmbedding_mulRight y) u ((fun h => h * y⁻¹) ⁻¹' 𝓕)
  rw [preimage_preimage_mul] at h1
  rw [h1]
  exact (isFundamentalDomain_mul_right μ Γ 𝓕 h𝓕 y⁻¹).setIntegral_eq h𝓕
    (fun g h => hu g g.2 h)
end GlobalTheory.DoubleCosetAdjoint
