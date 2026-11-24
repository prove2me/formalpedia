-- Prove2me | solution 1 for GlobalTheory.T.exists_scaled_nontrivial_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:06.70434+00:00
-- url     : https://prove2.me/submissions/5d61a5fa-51a6-40e3-91a3-e3a79080dcb1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsScaledNontrivialCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsScaledNontrivialCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CharConductor_exists_conductor_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k), valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧ ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | exact GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | (intros; apply GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step <;> assumption)
end _root_.GlobalTheory.T
