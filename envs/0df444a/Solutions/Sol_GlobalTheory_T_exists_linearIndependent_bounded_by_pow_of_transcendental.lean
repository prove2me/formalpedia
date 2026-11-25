-- Prove2me | solution 1 for GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:16:15.391917+00:00
-- url     : https://prove2.me/submissions/14e46d4b-6c8b-496b-bc5d-f9271c931af1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPowStatement
import Theorems.Thm_GlobalTheory_Nef_exists_many_bounded_by_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by
  first | exact @GlobalTheory.Nef.exists_many_bounded_by_pow | exact GlobalTheory.Nef.exists_many_bounded_by_pow | (intros; apply GlobalTheory.Nef.exists_many_bounded_by_pow <;> assumption)
end _root_.GlobalTheory.T
