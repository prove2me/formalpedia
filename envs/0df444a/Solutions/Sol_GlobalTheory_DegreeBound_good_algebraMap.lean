-- Prove2me | solution 1 for GlobalTheory.DegreeBound.good_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:50.720199+00:00
-- url     : https://prove2.me/submissions/3ecaaa38-d64a-4cca-9d92-177937e09a24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeLeOfIntegralAtInfinity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.DegreeBound
variable {K : Type} [Field K] {D : ℕ}
namespace GlobalTheory.DegreeBound
theorem _root_.solution (y : Fin D → K) (j : Fin D) (r : ℤ) : Good y j 0 (algebraMap ℤ K r) :=
  ⟨MvPolynomial.C r, by rw [totalDegree_C], by rw [pow_zero, mul_one, aeval_C]⟩
end GlobalTheory.DegreeBound
