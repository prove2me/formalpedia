-- Prove2me | solution 1 for GlobalTheory.T.double_coset_sum_fundamental_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:15.677365+00:00
-- url     : https://prove2.me/submissions/69c5a0e0-d4a9-4d0e-b9c2-c16ebd754489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomainStatement
import Theorems.Thm_GlobalTheory_doubleCosetSum_adjoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K : Subgroup H) [Countable Γ] (𝓕 : Set H) (x : H) (A A' : Finset H) (F F' : H → ℂ), IsFundamentalDomain Γ 𝓕 μ → (∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) → (∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) → A.card = A'.card → Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ γ ∈ Γ, ∀ h, F' (γ * h) = F' h) → (∀ k ∈ K, ∀ h, F (h * k) = F h) → (∀ k ∈ K, ∀ h, F' (h * k) = F' h) → IntegrableOn (fun h => star (F h) * F h) 𝓕 μ → IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ → ∫ h in 𝓕, star (∑ a ∈ A, F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F h) * ∑ a ∈ A', F' (h * a) ∂μ := by
  first | exact @GlobalTheory.doubleCosetSum_adjoint | exact GlobalTheory.doubleCosetSum_adjoint | (intros; apply GlobalTheory.doubleCosetSum_adjoint <;> assumption)
end _root_.GlobalTheory.T
