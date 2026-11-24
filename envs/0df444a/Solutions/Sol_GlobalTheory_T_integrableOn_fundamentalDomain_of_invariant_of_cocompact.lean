-- Prove2me | solution 1 for GlobalTheory.T.integrableOn_fundamentalDomain_of_invariant_of_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:15:00.516274+00:00
-- url     : https://prove2.me/submissions/83c9ddc9-b657-4e66-8114-313ed537f878

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IntegrableOnFundamentalDomainOfCocompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IntegrableOnFundamentalDomainOfCocompactStatement
import Theorems.Thm_GlobalTheory_integrableOn_fundamentalDomain_of_cocompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by
  first | exact @GlobalTheory.integrableOn_fundamentalDomain_of_cocompact | exact GlobalTheory.integrableOn_fundamentalDomain_of_cocompact | (intros; apply GlobalTheory.integrableOn_fundamentalDomain_of_cocompact <;> assumption)
end _root_.GlobalTheory.T
