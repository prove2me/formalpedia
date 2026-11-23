-- Prove2me | solution 1 for GlobalTheory.multiDiff_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:10.630649+00:00
-- url     : https://prove2.me/submissions/7f02bb8a-7c77-4b59-8f5a-6cbcf2f7717e

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
theorem _root_.solution {R : Type*} [CommRing R] {d : ℕ} (z : Fin d → R) (y : R) :
    multiDiff z (fun t ↦ t ^ d) y = d.factorial * ∏ i, z i := by
  simpa using multiDiff_polynomial_eval z (Polynomial.X ^ d) (Polynomial.natDegree_X_pow_le d) y
end GlobalTheory
