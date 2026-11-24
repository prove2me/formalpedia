-- Prove2me | solution 1 for GlobalTheory.T.reduction_to_siegel_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:51:43.116781+00:00
-- url     : https://prove2.me/submissions/b36c4f46-cb47-45a3-bba5-1557720fb3e9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ReductionToSiegelDomain
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ReductionToSiegelDomainStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Red_reduction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ (s : Finset SL(2, F)) (κ t : ℝ), 0 < κ ∧ 0 < t ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (∀ w, t ≤ (mob ρ (r * k) τ w).im) ∧ ∀ v w, κ * (mob ρ (r * k) τ w).im ≤ (mob ρ (r * k) τ v).im := by
  first | exact @GlobalTheory.CompanionTheory.SW.Red.reduction | exact GlobalTheory.CompanionTheory.SW.Red.reduction | (intros; apply GlobalTheory.CompanionTheory.SW.Red.reduction <;> assumption)
end _root_.GlobalTheory.T
