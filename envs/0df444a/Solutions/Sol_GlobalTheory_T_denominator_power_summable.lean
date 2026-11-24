-- Prove2me | solution 1 for GlobalTheory.T.denominator_power_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:20.041096+00:00
-- url     : https://prove2.me/submissions/7891b858-d79b-4aa9-a97c-83bcf3978bc2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummableStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DenSum_summable_den


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∀ M : ℕ, 3 ≤ M → ∀ N : ℕ, 0 < N → (∀ (b : F) (r : 𝓞 F), den (b + (r : F)) = den b) ∧ (∀ b : F, 0 < den b) ∧ ∀ s : Set F, (∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b') → Summable fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.SW.DenSum.summable_den | exact GlobalTheory.CompanionTheory.SW.DenSum.summable_den | (intros; apply GlobalTheory.CompanionTheory.SW.DenSum.summable_den <;> assumption)
end _root_.GlobalTheory.T
