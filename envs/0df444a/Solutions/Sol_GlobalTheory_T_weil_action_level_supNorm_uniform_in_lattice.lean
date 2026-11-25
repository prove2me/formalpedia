-- Prove2me | solution 1 for GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:52:45.40563+00:00
-- url     : https://prove2.me/submissions/dd27ed71-5030-49b1-bccc-b356c057b286

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Theorems.Thm_GlobalTheory_SW_weil_level_and_sup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ c R : ℕ, 0 < c → 0 < R → ∃ (R' : ℕ) (C : ℝ), 0 < R' ∧ ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, ∀ γ ∈ UU E N, Den c γ → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, LevelL Λ R φ → IsSB φ ∧ LevelL Λ R' (weil Ψ γ φ) ∧ ∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → ∀ x, ‖weil Ψ γ φ x‖ ≤ C * B := by
  first | exact @GlobalTheory.SW.weil_level_and_sup | exact GlobalTheory.SW.weil_level_and_sup | (intros; apply GlobalTheory.SW.weil_level_and_sup <;> assumption)
end _root_.GlobalTheory.T
