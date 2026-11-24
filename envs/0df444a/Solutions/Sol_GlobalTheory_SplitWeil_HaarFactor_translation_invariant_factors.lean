-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:09.809779+00:00
-- url     : https://prove2.me/submissions/17806f5e-e706-4a97-b026-4f76cbb11bd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_fiber_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_integrable_of_SB
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_exists_factor
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_basis_prod
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
namespace GlobalTheory.SplitWeil.HaarFactor
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (X₀ : Type) [TopologicalSpace X₀] [T2Space X₀] [LocallyCompactSpace X₀] [TotallyDisconnectedSpace X₀] (m₁ m₂ : Type) [Fintype m₁] [Fintype m₂] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × ((m₁ → k) × (m₂ → k))) →ₗ[ℂ] M), (∀ (a : (m₁ → k) × (m₂ → k)) (G G' : SB (X₀ × ((m₁ → k) × (m₂ → k)))), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G) → ∃ l₀ : SB X₀ →ₗ[ℂ] M, ∀ G, ∃ Ψ : SB X₀, (∀ x, Ψ.1 x = ∫ a₁, ∫ a₂, G.1 (x, (a₁, a₂)) ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν)) ∧ L G = l₀ Ψ := by
  intro k _ _ _ _ _ _ ν hν X₀ _ _ _ _ m₁ m₂ _ _ M _ _ L hL
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hν
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : (Measure.pi fun _ : m₁ => ν).IsAddHaarMeasure := inferInstance
  haveI : (Measure.pi fun _ : m₂ => ν).IsAddHaarMeasure := inferInstance
  obtain ⟨l₀, hl₀⟩ := exists_factor ((Measure.pi fun _ : m₁ => ν).prod (Measure.pi fun _ : m₂ => ν))
    (basis_prod m₁ m₂) L hL
  refine ⟨l₀, fun G => ?_⟩
  obtain ⟨Ψ, hΨ, hLG⟩ := hl₀ G
  refine ⟨Ψ, fun x => ?_, hLG⟩
  rw [hΨ x, integral_prod _ (integrable_of_SB _ (fiber_mem G.2 x))]
end GlobalTheory.SplitWeil.HaarFactor
