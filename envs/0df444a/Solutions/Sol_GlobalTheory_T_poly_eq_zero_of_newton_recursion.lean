-- Prove2me | solution 1 for GlobalTheory.T.poly_eq_zero_of_newton_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:20.498799+00:00
-- url     : https://prove2.me/submissions/83f03438-dc7c-48d2-b6d9-c39df0b4d805

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUnique
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUniqueStatement
import Theorems.Thm_GlobalTheory_newton_recursion_poly_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by
  first | exact @GlobalTheory.newton_recursion_poly_unique | exact GlobalTheory.newton_recursion_poly_unique | (intros; apply GlobalTheory.newton_recursion_poly_unique <;> assumption)
end _root_.GlobalTheory.T
