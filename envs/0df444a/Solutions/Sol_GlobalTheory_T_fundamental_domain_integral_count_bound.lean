-- Prove2me | solution 1 for GlobalTheory.T.fundamental_domain_integral_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:20:59.500005+00:00
-- url     : https://prove2.me/submissions/71afa956-98e0-40bb-aba9-89c6a03a5765

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainIntegralCountBound
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainIntegralCountBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Growth_lintegral_le_mul_of_encard_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (M : Set G), MeasurableSet M → ∀ (f : G → ℝ≥0∞), Measurable f →
    (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → ∀ n : ℕ, (∀ x, Set.encard {γ : Γ | (γ : G) * x ∈ M} ≤ n) →
    ∫⁻ x in M, f x ∂μ ≤ n * ∫⁻ x in 𝓕, f x ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le | exact GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le | (intros; apply GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le <;> assumption)
end _root_.GlobalTheory.T
