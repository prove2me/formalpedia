-- Prove2me | solution 1 for GlobalTheory.T.translationInvariant_schwartzBruhat_map_factors_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:48:20.090357+00:00
-- url     : https://prove2.me/submissions/b881efa4-cb1e-43df-90fe-2dbf1df839a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInteStatement
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_translation_invariant_factors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (X₀ : Type) [TopologicalSpace X₀] [T2Space X₀] [LocallyCompactSpace X₀] [TotallyDisconnectedSpace X₀] (m₁ m₂ : Type) [Fintype m₁] [Fintype m₂] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × ((m₁ → k) × (m₂ → k))) →ₗ[ℂ] M), (∀ (a : (m₁ → k) × (m₂ → k)) (G G' : SB (X₀ × ((m₁ → k) × (m₂ → k)))), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G) → ∃ l₀ : SB X₀ →ₗ[ℂ] M, ∀ G, ∃ Ψ : SB X₀, (∀ x, Ψ.1 x = ∫ a₁, ∫ a₂, G.1 (x, (a₁, a₂)) ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν)) ∧ L G = l₀ Ψ := by
  first | exact @GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors | exact GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors | (intros; apply GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors <;> assumption)
end _root_.GlobalTheory.T
