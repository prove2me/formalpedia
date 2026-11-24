-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.eval_map_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:49:09.273478+00:00
-- url     : https://prove2.me/submissions/eccf668b-569c-4cc2-b81b-e1b8c134d2ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
open GlobalTheory GlobalTheory.SimpleRoots
variable {d : ℕ}
namespace GlobalTheory.SimpleRoots
theorem _root_.solution (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x : Fin d → ℂ) (y : ℂ) :
    (p.map (MvPolynomial.eval x)).eval y
      = ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval x (p.coeff i) * y ^ i := by
  rw [eval_map, eval₂_eq_sum_range]
end GlobalTheory.SimpleRoots
