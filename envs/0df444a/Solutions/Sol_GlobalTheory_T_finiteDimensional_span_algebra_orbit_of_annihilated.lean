-- Prove2me | solution 1 for GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:21:07.855102+00:00
-- url     : https://prove2.me/submissions/160fa67c-c85c-4ad2-a7b2-d6fc193f7b04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilatedStatement
import Theorems.Thm_GlobalTheory_killed_span_adjoin_finrank_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤ ∏ t ∈ T, (p t).natDegree := by
  first | exact @GlobalTheory.killed_span_adjoin_finrank_le | exact GlobalTheory.killed_span_adjoin_finrank_le | (intros; apply GlobalTheory.killed_span_adjoin_finrank_le <;> assumption)
end _root_.GlobalTheory.T
