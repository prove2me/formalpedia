-- Prove2me | solution 1 for GlobalTheory.T.annihilator_of_annihilator_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:23:49.267108+00:00
-- url     : https://prove2.me/submissions/46057394-f018-48e6-8ea2-4cc1d3b2fa40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_selfDual_of_between


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
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (μ : Measure V), μ.IsAddHaarMeasure → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → ∀ L₁ L L₂ : AddSubgroup V, L₁ ≤ L → L ≤ L₂ → IsOpen (L₁ : Set V) → IsCompact (L₂ : Set V) → IsCompact (perp χ L₁) → IsOpen (perp χ L₂) → perp χ (perp χ L₁) ⊆ L₁ → perp χ (perp χ L₂) ⊆ L₂ → μ L₁ * μ (perp χ L₁) = 1 → μ L₂ * μ (perp χ L₂) = 1 → IsCompact (perp χ L) ∧ IsOpen (perp χ L) ∧ perp χ (perp χ L) ⊆ L ∧ μ L * μ (perp χ L) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.CofinalDual.selfDual_of_between | exact GlobalTheory.CompanionTheory.SW.CofinalDual.selfDual_of_between | (intros; apply GlobalTheory.CompanionTheory.SW.CofinalDual.selfDual_of_between <;> assumption)
end _root_.GlobalTheory.T
