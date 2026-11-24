-- Prove2me | solution 1 for GlobalTheory.T.exists_alternating_form_left_corank_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:49.178982+00:00
-- url     : https://prove2.me/submissions/e85b2b55-2396-46fb-bffc-7f9c2b360c19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOneStatement
import Theorems.Thm_GlobalTheory_AltCorank_exists_alt_corank_le_one


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
theorem _root_.solution : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] (S₁ S₂ : Submodule K V), Module.finrank K S₁ = Module.finrank K S₂ → ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) → (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x := by
  first | exact @GlobalTheory.AltCorank.exists_alt_corank_le_one | exact GlobalTheory.AltCorank.exists_alt_corank_le_one | (intros; apply GlobalTheory.AltCorank.exists_alt_corank_le_one <;> assumption)
end _root_.GlobalTheory.T
