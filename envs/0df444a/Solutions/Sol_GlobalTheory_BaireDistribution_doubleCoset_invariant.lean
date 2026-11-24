-- Prove2me | solution 1 for GlobalTheory.BaireDistribution.doubleCoset_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:18.028841+00:00
-- url     : https://prove2.me/submissions/2772ac04-5973-4f88-9093-39590d2d474d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BaireDistribution
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
omit [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.BaireDistribution
theorem _root_.solution (K : Subgroup G) (x : G) : ∀ a ∈ K, ∀ b ∈ K, ∀ g,
    a * g * b ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} ↔
      g ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} := by
  intro a ha b hb g
  constructor
  · rintro ⟨c, hc, d, hd, h⟩
    refine ⟨a⁻¹ * c, K.mul_mem (K.inv_mem ha) hc, d * b⁻¹, K.mul_mem hd (K.inv_mem hb), ?_⟩
    have : g = a⁻¹ * (a * g * b) * b⁻¹ := by group
    rw [this, h]; group
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact ⟨a * c, K.mul_mem ha hc, d * b, K.mul_mem hd hb, by group⟩
end GlobalTheory.BaireDistribution
