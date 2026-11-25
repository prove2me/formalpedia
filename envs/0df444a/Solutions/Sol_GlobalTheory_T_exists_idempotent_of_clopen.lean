-- Prove2me | solution 1 for GlobalTheory.T.exists_idempotent_of_clopen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:22:01.282201+00:00
-- url     : https://prove2.me/submissions/196ef803-40f5-4707-90e7-6b5763442b53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopen
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopenStatement
import Theorems.Thm_GlobalTheory_exists_idempotent_basicOpen_eq_of_isClopen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}) (U : Set X), IsClopen U → ∃ e : Γ(X, ⊤), e * e = e ∧ ((X.basicOpen e : X.Opens) : Set X) = U := by
  first | exact @GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen | exact GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen | (intros; apply GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen <;> assumption)
end _root_.GlobalTheory.T
