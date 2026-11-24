-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.exists_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:57.364048+00:00
-- url     : https://prove2.me/submissions/dcfb2c65-1a03-4a37-9afd-6f369c72d6f7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianMatricesModPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (h : IsUnrQuad R σ ϖ q ε) : ∃ u θ : R, IsUnit (u - σ u) ∧ θ + σ θ = 1 := by
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hσ : σ (u - σ u) = -(u - σ u) := by rw [map_sub, h.inv]; ring
  have hsv : σ v = -v := by
    have h1 : σ (u - σ u) * σ v = 1 := by rw [← map_mul, hv, map_one]
    rw [hσ] at h1
    have h2 : (u - σ u) * (σ v + v) = 0 := by linear_combination (-1 : R) * h1 + hv
    have h3 : v * ((u - σ u) * (σ v + v)) = 0 := by rw [h2, mul_zero]
    rw [← mul_assoc, mul_comm v, hv, one_mul] at h3
    linear_combination h3
  refine ⟨u, u * v, hu, ?_⟩
  rw [map_mul, hsv]
  linear_combination hv
end GlobalTheory.CompanionTheory.UnrDens
