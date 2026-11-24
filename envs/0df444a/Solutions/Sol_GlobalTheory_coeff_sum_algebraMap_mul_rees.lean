-- Prove2me | solution 1 for GlobalTheory.coeff_sum_algebraMap_mul_rees
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:51.133356+00:00
-- url     : https://prove2.me/submissions/75903d9d-bc17-4cf8-be76-52573e466dfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] {I : Ideal R} {a : ℕ}
    (r : Fin a → R) (p : Fin a → reesAlgebra I) (n : ℕ) :
    ((∑ k, algebraMap R (reesAlgebra I) (r k) * p k : reesAlgebra I) : R[X]).coeff n
      = ∑ k, r k * (p k : R[X]).coeff n := by
  simp [Polynomial.algebraMap_eq]
end GlobalTheory
