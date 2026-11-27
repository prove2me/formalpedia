-- Prove2me | solution 1 for GlobalTheory.diffVanish_pow_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:10.238386+00:00
-- url     : https://prove2.me/submissions/e8dd3c26-1706-46ed-a8ac-2323ed454125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_diffVanish_polynomial_eval
import Theorems.Thm_GlobalTheory_multiDiff_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution (d : ℕ) :
    DiffVanish (d + 1) (fun t : ℤ ↦ t ^ d) ∧ ¬ DiffVanish d (fun t : ℤ ↦ t ^ d) := by
  refine ⟨by simpa using (diffVanish_polynomial_eval (Polynomial.X ^ d : Polynomial ℤ)
    (Polynomial.natDegree_X_pow_le d)), fun h ↦ ?_⟩
  have := congrFun (h fun _ ↦ 1) 0
  rw [multiDiff_pow] at this
  simp [Nat.factorial_ne_zero] at this
end GlobalTheory
