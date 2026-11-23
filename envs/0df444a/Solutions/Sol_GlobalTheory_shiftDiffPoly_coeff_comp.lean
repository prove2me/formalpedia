-- Prove2me | solution 1 for GlobalTheory.shiftDiffPoly_coeff_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:35.183842+00:00
-- url     : https://prove2.me/submissions/eceb825a-79b1-4080-8b63-1c9f3d0001e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUnique

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
theorem _root_.solution (f : ℂ[X]) (n : ℕ) :
    (f.comp (X + 1)).coeff n = ∑ i ∈ range (f.natDegree + 1), f.coeff i * (i.choose n : ℂ) := by
  rw [comp, eval₂_eq_sum_range]
  simp [finset_sum_coeff, coeff_C_mul, coeff_X_add_one_pow]
end GlobalTheory
