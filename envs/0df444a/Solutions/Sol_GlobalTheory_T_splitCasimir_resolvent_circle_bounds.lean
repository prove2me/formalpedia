-- Prove2me | solution 1 for GlobalTheory.T.splitCasimir_resolvent_circle_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:59.370819+00:00
-- url     : https://prove2.me/submissions/aae8af1b-bb6a-45cb-8993-c4bf3dd11a63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirResolventCircleBounds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirResolventCircleBoundsStatement
import Theorems.Thm_GlobalTheory_splitCas_resolvent_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → (∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → (13 * bv / 32) ^ 2 * ∑ c, ‖x c‖ ^ 2 ≤ ∑ c, ‖ζ • x c - splitCas E x c‖ ^ 2) ∧ ∑ c, ‖splitCas E x c‖ ^ 2 ≤ (3 * bv) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  first | exact @GlobalTheory.splitCas_resolvent_bounds | exact GlobalTheory.splitCas_resolvent_bounds | (intros; apply GlobalTheory.splitCas_resolvent_bounds <;> assumption)
end _root_.GlobalTheory.T
