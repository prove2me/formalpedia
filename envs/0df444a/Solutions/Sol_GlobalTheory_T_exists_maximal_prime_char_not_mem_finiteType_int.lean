-- Prove2me | solution 1 for GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:21:23.088672+00:00
-- url     : https://prove2.me/submissions/0656ffd9-48fb-4dfa-89d5-4d588d8a2259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalPrimeCharNotMemFiniteTypeInt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalPrimeCharNotMemFiniteTypeIntStatement
import Theorems.Thm_GlobalTheory_closedPt_of_finiteType_int


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  first | exact @GlobalTheory.closedPt_of_finiteType_int | exact GlobalTheory.closedPt_of_finiteType_int | (intros; apply GlobalTheory.closedPt_of_finiteType_int <;> assumption)
end _root_.GlobalTheory.T
