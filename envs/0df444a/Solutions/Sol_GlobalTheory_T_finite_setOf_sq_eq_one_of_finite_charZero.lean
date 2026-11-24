-- Prove2me | solution 1 for GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:39.781239+00:00
-- url     : https://prove2.me/submissions/dbefa169-9df8-459c-bc75-fad1812e03b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSqEqOneOfFiniteAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSqEqOneOfFiniteAlgebraStatement
import Theorems.Thm_GlobalTheory_finite_sq_eq_one_of_finite_algebra


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
theorem _root_.solution : ∀ (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Set.Finite {x : A | x ^ 2 = 1} := by
  first | exact @GlobalTheory.finite_sq_eq_one_of_finite_algebra | exact GlobalTheory.finite_sq_eq_one_of_finite_algebra | (intros; apply GlobalTheory.finite_sq_eq_one_of_finite_algebra <;> assumption)
end _root_.GlobalTheory.T
