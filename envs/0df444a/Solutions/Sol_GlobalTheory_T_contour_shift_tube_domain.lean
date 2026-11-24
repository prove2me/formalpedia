-- Prove2me | solution 1 for GlobalTheory.T.contour_shift_tube_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:30.873651+00:00
-- url     : https://prove2.me/submissions/e16cbed1-4d67-4d68-9735-91e5863c0a1e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomain
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomainStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
    ∀ H : (ι → ℂ) → ℂ, DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω} →
    (∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2)) →
    ∀ x₁ ∈ Ω, ∀ x₂ ∈ Ω,
      (∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I)) =
        ∫ y : ι → ℝ, H (fun i => (x₂ i : ℂ) + (y i : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.tubeShift | exact GlobalTheory.CompanionTheory.EisTube.tubeShift | (intros; apply GlobalTheory.CompanionTheory.EisTube.tubeShift <;> assumption)
end _root_.GlobalTheory.T
