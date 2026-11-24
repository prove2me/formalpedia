-- Prove2me | solution 1 for GlobalTheory.diffVanish_polynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:47.83108+00:00
-- url     : https://prove2.me/submissions/1501a982-b27d-4c25-9521-2fdddb7f9557

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_polynomial_eval

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
theorem _root_.solution {R : Type*} [CommRing R] {d : ℕ} (p : Polynomial R)
    (hp : p.natDegree ≤ d) : DiffVanish (d + 1) (fun t ↦ p.eval t) := fun z ↦ by
  ext y
  rw [multiDiff_polynomial_eval z p (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  simp
end GlobalTheory
