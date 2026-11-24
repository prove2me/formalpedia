-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:14.470021+00:00
-- url     : https://prove2.me/submissions/2928de63-3503-445c-b8ad-19afd564ded8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Theorems.Thm_GlobalTheory_SW_ip_self_nonneg_and_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → (ip φ φ).im = 0 ∧ 0 ≤ (ip φ φ).re ∧ (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * (ip φ φ).re) ∧ (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (ip φ φ).re ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧ (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, IsSB ψ → ‖ip φ ψ‖ ^ 2 ≤ (ip φ φ).re * (ip ψ ψ).re := by
  first | exact @GlobalTheory.SW.ip_self_nonneg_and_bounds | exact GlobalTheory.SW.ip_self_nonneg_and_bounds | (intros; apply GlobalTheory.SW.ip_self_nonneg_and_bounds <;> assumption)
end _root_.GlobalTheory.T
