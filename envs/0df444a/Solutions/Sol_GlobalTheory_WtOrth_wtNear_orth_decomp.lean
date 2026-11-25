-- Prove2me | solution 1 for GlobalTheory.WtOrth.wtNear_orth_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:49:28.0768+00:00
-- url     : https://prove2.me/submissions/b5e4e162-bec9-4af4-b756-9f9091856065

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecomp
import Theorems.Thm_GlobalTheory_WtOrth_inner_eq_zero_of_ne
import Theorems.Thm_GlobalTheory_WtOrth_exists_decomp

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
open GlobalTheory GlobalTheory.WtOrth
namespace GlobalTheory.WtOrth
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t ∧ IsWeight E ω (x ω)) ∧ w = ∑ ω ∈ T, x ω ∧ ∀ ω ∈ T, ∀ ω' ∈ T, ω ≠ ω' → ⟪x ω, x ω'⟫_ℂ = 0 := by
  intro M _ _ n ε E Λ t w hU hw
  obtain ⟨T, x, h1, h2, _, h4⟩ := exists_decomp E Λ t w hw
  exact ⟨T, x, fun ω h => ⟨h1 ω h, h2 ω⟩, h4,
    fun ω _ ω' _ hne => inner_eq_zero_of_ne hU (h2 ω) (h2 ω') hne⟩
end GlobalTheory.WtOrth
