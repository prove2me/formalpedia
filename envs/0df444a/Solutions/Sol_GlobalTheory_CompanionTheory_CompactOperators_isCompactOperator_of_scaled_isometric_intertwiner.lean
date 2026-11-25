-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CompactOperators.isCompactOperator_of_scaled_isometric_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:35:42.66384+00:00
-- url     : https://prove2.me/submissions/4d9ddc02-5200-47fd-967c-1d71cbbb22ce

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactOperatorOfScaledIsometricIntertwiner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CompactOperators
namespace GlobalTheory.CompanionTheory.CompactOperators
theorem _root_.solution
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) (Φ : H →L[ℂ] K) (c : ℝ) (hc : 0 < c)
    (hΦ : ∀ x, ‖Φ x‖ = c * ‖x‖) (hAB : Φ ∘L A = B ∘L Φ) (hB : IsCompactOperator B) :
    IsCompactOperator A := by
  have hcn : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) Φ := by
    refine Φ.antilipschitz_of_bound fun x => ?_
    rw [Real.coe_toNNReal _ hcn, hΦ, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hemb : IsClosedEmbedding Φ := hanti.isClosedEmbedding Φ.uniformContinuous
  obtain ⟨S, hS, hSn⟩ := hB
  refine ⟨Φ ⁻¹' S, hemb.isCompact_preimage hS, ?_⟩
  have hpre : A ⁻¹' (Φ ⁻¹' S) = Φ ⁻¹' (B ⁻¹' S) := by
    ext x
    show Φ (A x) ∈ S ↔ B (Φ x) ∈ S
    rw [show Φ (A x) = B (Φ x) from ContinuousLinearMap.ext_iff.mp hAB x]
  rw [hpre]
  exact Φ.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hSn)
end GlobalTheory.CompanionTheory.CompactOperators
