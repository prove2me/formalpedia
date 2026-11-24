-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.laplaceEntire_firstCountable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:17:32.537882+00:00
-- url     : https://prove2.me/submissions/53b92a1d-d39f-42a4-973c-3fc13fdf8c40

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftParametrisedIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_laplaceEntire


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (P : Type u) [TopologicalSpace P] [FirstCountableTopology P] (h : P → ℝ), (∀ p, 0 ≤ h p) →
    (∀ p, ∃ U ∈ nhds p, BddAbove (h '' U)) →
    ∀ ψ : P → (ι → ℝ) → ℂ, (∀ p, MeasureTheory.AEStronglyMeasurable (ψ p)) →
    (∀ t, Continuous (fun p => ψ p t)) →
    (∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i))) →
    (∀ p (z : ι → ℂ), MeasureTheory.Integrable
        (fun t : ι → ℝ => ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    (∀ p, Differentiable ℂ (fun z : ι → ℂ =>
        ∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    Continuous (fun q : (ι → ℂ) × P =>
        ∫ t : ι → ℝ, ψ q.2 t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, q.1 i * t i)) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p,
        ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖ ≤ C * h p) :=
  fun ι _ P _ _ h hh hloc ψ hm hc hv => laplaceEntire ι P h hh hloc ψ hm hc hv
end GlobalTheory.CompanionTheory.EisTube
