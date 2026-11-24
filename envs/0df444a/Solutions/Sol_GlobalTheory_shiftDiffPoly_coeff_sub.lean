-- Prove2me | solution 1 for GlobalTheory.shiftDiffPoly_coeff_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:45.87087+00:00
-- url     : https://prove2.me/submissions/c9fd5090-aa86-49d1-a2d9-7f47924a3ff7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUnique
import Theorems.Thm_GlobalTheory_shiftDiffPoly_coeff_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (f : ℂ[X]) (e : ℕ) (he : f.natDegree = e + 1) :
    (f.comp (X + 1) - f).coeff e = ((e : ℂ) + 1) * f.coeff (e + 1) := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, he, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero]
  · simp [Nat.choose_succ_self_right]; ring
  · intro i hi
    simp at hi
    simp [Nat.choose_eq_zero_of_lt hi]
end GlobalTheory
