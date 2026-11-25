-- Prove2me | solution 1 for GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:26:39.94428+00:00
-- url     : https://prove2.me/submissions/5b833ee3-a595-44e5-ae8e-8c6555220808

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LintegralFundamentalDomainLeOfMeetsOrbits
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LintegralFundamentalDomainLeOfMeetsOrbitsStatement
import Theorems.Thm_GlobalTheory_lintegral_fundamentalDomain_le_of_meets_orbits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}, IsFundamentalDomain Γ 𝓕 ν → MeasurableSet S → (∀ g, ∃ γ ∈ Γ, γ * g ∈ S) → ∀ {f : G → ℝ≥0∞}, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  first | exact @GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits | exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits | (intros; apply GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits <;> assumption)
end _root_.GlobalTheory.T
