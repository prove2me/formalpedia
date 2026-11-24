-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhat_distribution_eq_zero_baire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:22:30.132473+00:00
-- url     : https://prove2.me/submissions/629323d6-93dc-4cb7-8e2f-ab59463fa15d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaireStatement
import Theorems.Thm_GlobalTheory_BaireDistribution_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (ι : Type) [Countable ι] (K : ι → ℕ → Subgroup G), (∀ i m, IsOpen (K i m : Set G) ∧ IsCompact (K i m : Set G)) → (∀ i, ∀ U ∈ nhds (1 : G), ∃ m, (K i m : Set G) ⊆ U) → ∀ D : SB G →ₗ[ℂ] ℂ, (∀ x : G, ∃ i, ∀ (m : ℕ) (φ : SB G), φ.1 = Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0) → D = 0 := by
  first | exact @GlobalTheory.BaireDistribution.eq_zero | exact GlobalTheory.BaireDistribution.eq_zero | (intros; apply GlobalTheory.BaireDistribution.eq_zero <;> assumption)
end _root_.GlobalTheory.T
