-- Prove2me | solution 1 for GlobalTheory.T.fundamental_domain_fibration_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:14.414775+00:00
-- url     : https://prove2.me/submissions/e2e8ec89-4d72-4714-b73e-ef5c7307bd15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFibrationVolume
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFibrationVolumeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PeriodisedMean_setLIntegral_tsum_comp_inv_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by
  first | exact @GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq | exact GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq | (intros; apply GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq <;> assumption)
end _root_.GlobalTheory.T
