-- Prove2me | solution 1 for GlobalTheory.T.exists_orthogonal_weight_decomp_of_mem_wtNear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:26.713925+00:00
-- url     : https://prove2.me/submissions/84798727-3764-4fb9-be6f-5c9000236f87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecomp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecompStatement
import Theorems.Thm_GlobalTheory_WtOrth_wtNear_orth_decomp


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
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t ∧ IsWeight E ω (x ω)) ∧ w = ∑ ω ∈ T, x ω ∧ ∀ ω ∈ T, ∀ ω' ∈ T, ω ≠ ω' → ⟪x ω, x ω'⟫_ℂ = 0 := by
  first | exact @GlobalTheory.WtOrth.wtNear_orth_decomp | exact GlobalTheory.WtOrth.wtNear_orth_decomp | (intros; apply GlobalTheory.WtOrth.wtNear_orth_decomp <;> assumption)
end _root_.GlobalTheory.T
